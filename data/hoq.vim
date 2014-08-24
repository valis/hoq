if version < 600
  syn clear
elseif exists("b:current_syntax")
  finish
endif

syn keyword hoqKeyword         import case of infix infixl infixr
syn keyword hoqConstructor     left right path coe iso squeeze contr
syn keyword hoqType            data I Path with Contr Prop record fields constructor where
syn match   hoqLineComment     "---*\([^-!#$%&\*\+./<=>\?@\\^|~].*\)\?$"
syn region  hoqBlockComment    start="{-"  end="-}" contains=hoqBlockComment
syn match   hoqNumber          "\<[0-9]\+\>"
syn match   hoqType            "\<Type[0-9]*\>"
syn match   hoqType            "\<Set[0-9]*\>"
" syn match   hoqDelimiter       "(\|)\|;\|_\|{\|}"
syn match   hoqOperator        "=\|:\|->\|\\\|@"

if version >= 508 || !exists("did_hoq_syntax_inits")
  if version < 508
    let did_hoq_syntax_inits = 1
    command -nargs=+ HiLink hi link <args>
  else
    command -nargs=+ HiLink hi def link <args>
  endif

  HiLink hoqKeyword        Keyword
  HiLink hoqConstructor    Keyword
  HiLink hoqLineComment    hoqComment
  HiLink hoqBlockComment   hoqComment
  HiLink hoqComment        Comment
  HiLink hoqNumber         Number
  HiLink hoqType           Type
  HiLink hoqDelimiter      Delimiter
  HiLink hoqOperator       Operator

  delcommand HiLink
endif

let b:current_syntax = "hoq"
