/-
  The part of OCaml's standard-library module `Format` used by CompCert's
  pretty-printers (`backend/PrintCminor.ml`, `cfrontend/PrintClight.ml`,
  `cfrontend/PrintCsyntax.ml`, …).

  OCaml's printers call `fprintf p "...@[<hov 2>...@ ...@]"`: the format
  string mixes text with *boxes* (`@[<kind n>` … `@]`) and *break hints*
  (`@ `, `@,`, `@;<n m>`).  The `Format` engine decides where to break lines
  so that the text fits in the right margin.  Here a printer produces a
  `Doc`, the sequence of tokens that `Format` would enqueue, and `render`
  lays it out with the same algorithm as OCaml's `Format` (the scanning of
  token sizes, `format_pp_token`, `break_new_line`, `break_same_line`,
  `pp_force_break_line`), with the defaults of a formatter on an output
  channel: margin 78, maximal indentation 68.

  `ppf "..."` parses the formatting directives of a string literal (only
  the directives; data is inserted with `txt`), so that
  `fprintf p "@[<hv 2>%s =@ %a;@]" x print_expr e` becomes
  `ppf "@[<hv 2>" ++ txt x ++ ppf " =@ " ++ printExpr e ++ ppf ";@]"`.

  Differences: the engine sees the whole document at once instead of a
  stream.  This gives the same sizes as OCaml's bounded look-ahead (a token
  whose size OCaml does not know yet is printed as "too large", and its
  actual size is then larger than the remaining space anyway).  Tags,
  tabulation boxes and the limit on the number of open boxes
  (`pp_max_boxes`) are not supported.  A newline character in the text is
  output as is and counts for one column, as in OCaml.
-/

namespace CC
namespace Format

/-- The kinds of boxes (`Pp_hbox`, `Pp_vbox`, `Pp_hvbox`, `Pp_hovbox`,
    `Pp_box`).  `fits` is the engine's `Pp_fits`: a box that fits on the
    line. -/
inductive BoxKind where
  | h | v | hv | hov | b | fits
  deriving DecidableEq, Repr, Inhabited

/-- The tokens of `Format`'s queue. -/
inductive Tok where
  /-- `Pp_text` -/
  | text (s : String)
  /-- `Pp_break` with `nspaces` and `offset` (`@;<n m>`) -/
  | brk (n : Nat) (off : Int)
  /-- `Pp_begin` (`@[<kind indent>`) -/
  | begin (indent : Int) (k : BoxKind)
  /-- `Pp_end` (`@]`) -/
  | close
  /-- `Pp_newline` (`@\n`, `pp_force_newline`) -/
  | newline
  /-- `@.` (`pp_print_newline`): close the open boxes, flush, newline -/
  | flushNewline
  deriving Repr, Inhabited

/-- A document: the tokens a printer enqueues. -/
abbrev Doc := Array Tok

/-- `pp_print_string` -/
def txt (s : String) : Doc := #[.text s]

/-- Parse the box kind and indentation of `@[<kind n>`. -/
def parseBoxSpec (spec : String) : BoxKind × Int :=
  let ws := (spec.splitOn " ").filter (· ≠ "")
  let kind : BoxKind := match ws.head? with
    | some "h" => .h | some "v" => .v | some "hv" => .hv
    | some "hov" => .hov | some "b" => .b | _ => .b
  let ind : Int := match ws.drop 1 with
    | n :: _ => (n.toInt?).getD 0
    | [] => 0
  (kind, ind)

/-- Parse `n m` of `@;<n m>`. -/
def parseBreakSpec (spec : String) : Nat × Int :=
  let ws := (spec.splitOn " ").filter (· ≠ "")
  match ws with
  | [n, m] => ((n.toNat?).getD 1, (m.toInt?).getD 0)
  | [n] => ((n.toNat?).getD 1, 0)
  | _ => (1, 0)

/-- Parse the formatting directives of a format-string literal. -/
partial def ppf (s : String) : Doc := Id.run do
  let cs := s.toList.toArray
  let mut out : Doc := #[]
  let mut buf : String := ""
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '@' && i + 1 < cs.size then
      let d := cs[i+1]!
      let flush := fun (out : Doc) (buf : String) => if buf.isEmpty then out else out.push (.text buf)
      if d == '[' then
        out := flush out buf; buf := ""
        if i + 2 < cs.size && cs[i+2]! == '<' then
          let mut j := i + 3
          let mut spec := ""
          while j < cs.size && cs[j]! != '>' do
            spec := spec.push cs[j]!; j := j + 1
          let (k, ind) := parseBoxSpec spec
          out := out.push (.begin ind k); i := j + 1
        else
          out := out.push (.begin 0 .b); i := i + 2
      else if d == ']' then
        out := flush out buf; buf := ""; out := out.push .close; i := i + 2
      else if d == ' ' then
        out := flush out buf; buf := ""; out := out.push (.brk 1 0); i := i + 2
      else if d == ',' then
        out := flush out buf; buf := ""; out := out.push (.brk 0 0); i := i + 2
      else if d == ';' then
        out := flush out buf; buf := ""
        if i + 2 < cs.size && cs[i+2]! == '<' then
          let mut j := i + 3
          let mut spec := ""
          while j < cs.size && cs[j]! != '>' do
            spec := spec.push cs[j]!; j := j + 1
          let (n, m) := parseBreakSpec spec
          out := out.push (.brk n m); i := j + 1
        else
          out := out.push (.brk 1 0); i := i + 2
      else if d == '.' then
        out := flush out buf; buf := ""; out := out.push .flushNewline; i := i + 2
      else if d == '\n' then
        out := flush out buf; buf := ""; out := out.push .newline; i := i + 2
      else if d == '@' then
        buf := buf.push '@'; i := i + 2
      else
        buf := buf.push c; i := i + 1
    else
      buf := buf.push c; i := i + 1
  if !buf.isEmpty then out := out.push (.text buf)
  return out

/-- "Infinite" size (`pp_infinity`). -/
def infinity : Int := 1000000010

/-- The length of a token (`length` of the queue element). -/
def Tok.len : Tok → Int
  | .text s => s.utf8ByteSize
  | .brk n _ => n
  | _ => 0

/-- The sizes OCaml's scanning computes (`set_size`, `scan_push`): the
    size of a text is its length; the size of a break is its width plus the
    length of what follows up to the next break of the same box or the end
    of the box; the size of a box is its length when printed on one line.
    Sizes that stay unknown are infinite. -/
def sizes (toks : Array Tok) : Array Int := Id.run do
  let mut sz : Array Int := toks.map fun t => match t with
    | .text s => (s.utf8ByteSize : Int) | _ => infinity
  let mut rt : Int := 0
  -- the scan stack: (token index, right total at push)
  let mut stack : List (Nat × Int) := []
  for h : i in [0:toks.size] do
    match toks[i] with
    | .brk n _ =>
      -- `set_size state true`
      match stack with
      | (j, l) :: rest =>
        if let .brk .. := toks[j]! then
          sz := sz.set! j (rt - l); stack := rest
      | [] => pure ()
      stack := (i, rt) :: stack
      rt := rt + n
    | .begin .. =>
      stack := (i, rt) :: stack
    | .close =>
      match stack with
      | (j, l) :: rest =>
        if let .brk .. := toks[j]! then
          sz := sz.set! j (rt - l); stack := rest
      | [] => pure ()
      match stack with
      | (j, l) :: rest =>
        if let .begin .. := toks[j]! then
          sz := sz.set! j (rt - l); stack := rest
      | [] => pure ()
    | .text s => rt := rt + s.utf8ByteSize
    | _ => pure ()
  return sz

/-- The state of the engine. -/
structure State where
  margin : Int := 78
  maxIndent : Int := 68
  spaceLeft : Int := 78
  currentIndent : Int := 0
  isNewLine : Bool := true
  /-- `pp_format_stack`: box kind and `width` -/
  stack : List (BoxKind × Int) := [(.hov, 78)]
  out : Array String := #[]

/-- `n` blanks. -/
def blanks (n : Int) : String := String.ofList (List.replicate n.toNat ' ')

/-- `break_new_line` -/
def breakNewLine (st : State) (off width : Int) : State :=
  let indent := st.margin - width + off
  let real := min st.maxIndent indent
  { st with out := (st.out.push "\n").push (blanks real), isNewLine := true,
            currentIndent := real, spaceLeft := st.margin - real }

/-- `break_same_line` -/
def breakSameLine (st : State) (n : Int) : State :=
  { st with spaceLeft := st.spaceLeft - n, out := st.out.push (blanks n) }

/-- `format_pp_token` -/
def formatToken (st : State) (size : Int) : Tok → State
  | .text s =>
    { st with spaceLeft := st.spaceLeft - s.utf8ByteSize, out := st.out.push s,
              isNewLine := false }
  | .begin off k =>
    let insertion := st.margin - st.spaceLeft
    -- `pp_force_break_line`
    let st := if insertion > st.maxIndent then
        match st.stack with
        | (bk, width) :: _ =>
          if width > st.spaceLeft then
            (match bk with | .fits | .h => st | _ => breakNewLine st 0 width)
          else st
        | [] => st
      else st
    let width := st.spaceLeft - off
    let k' := if k == .v then .v else if size > st.spaceLeft then k else .fits
    { st with stack := (k', width) :: st.stack }
  | .close => { st with stack := st.stack.tail }
  | .brk n off =>
    match st.stack with
    | [] => st
    | (bk, width) :: _ =>
      match bk with
      | .hov => if size > st.spaceLeft then breakNewLine st off width else breakSameLine st n
      | .b =>
        if st.isNewLine then breakSameLine st n
        else if size > st.spaceLeft then breakNewLine st off width
        else if st.currentIndent > st.margin - width + off then breakNewLine st off width
        else breakSameLine st n
      | .hv | .v => breakNewLine st off width
      | .fits | .h => breakSameLine st n
  | .newline =>
    match st.stack with
    | (_, width) :: _ => breakNewLine st 0 width
    | [] => { st with out := st.out.push "\n" }
  | .flushNewline => st

/-- Lay out one segment (a part of the document between two `@.`): close
    the boxes left open, compute the sizes, and print. -/
def renderSegment (st : State) (toks : Array Tok) : State := Id.run do
  let mut depth : Nat := 0
  for t in toks do
    match t with
    | .begin .. => depth := depth + 1
    | .close => depth := depth - 1
    | _ => pure ()
  let toks := toks ++ (Array.replicate depth Tok.close)
  let sz := sizes toks
  let mut st := st
  for h : i in [0:toks.size] do
    st := formatToken st sz[i]! toks[i]
  return st

/-- Lay out a document with the default margins of a formatter on an
    output channel; the result is the text OCaml's `Format` would print. -/
def render (d : Doc) (margin : Int := 78) (maxIndent : Int := 68) : String := Id.run do
  let init : State := { margin, maxIndent, spaceLeft := margin, stack := [(.hov, margin)] }
  let mut st := init
  let mut seg : Array Tok := #[]
  for t in d do
    match t with
    | .flushNewline =>
      st := renderSegment st seg
      st := { init with out := st.out.push "\n" }
      seg := #[]
    | t => seg := seg.push t
  st := renderSegment st seg
  return String.join st.out.toList

#guard render (ppf "@[<hov 2>aaa@ bbb@ ccc@]@.") = "aaa bbb ccc\n"
#guard render (ppf "@[<v 2>{@ x;@ y;@;<0 -2>}@]@.") = "{\n  x;\n  y;\n}\n"
#guard render (ppf "@[<hv 2>f(@,a,@ b)@]") = "f(a, b)"
#guard render (ppf "@[<hov 2>" ++ txt (String.ofList (List.replicate 70 'a')) ++
    ppf "@ bbbbbbbbbbbb@]") =
  String.ofList (List.replicate 70 'a') ++ "\n  bbbbbbbbbbbb"
#guard render (ppf "@[<hv 2>" ++ txt (String.ofList (List.replicate 70 'a')) ++
    ppf "@ b@ c@]") =
  String.ofList (List.replicate 70 'a') ++ " b c"
#guard render (ppf "@[<hv 2>" ++ txt (String.ofList (List.replicate 76 'a')) ++
    ppf "@ b@ c@]") =
  String.ofList (List.replicate 76 'a') ++ "\n  b\n  c"

end Format
end CC
