"Author: Nachum Kanovsky
"Email: nkanovsky yahoo com
"Version: 1.3
if exists("b:current_syntax")
	finish
endif

let b:current_syntax = "systemverilog"

syntax keyword svTodo TODO contained
syntax match svLineComment "//.*" contains=svTodo
syntax region svBlockComment start="/\*" end="\*/" contains=svTodo
syntax keyword svBoolean true false TRUE FALSE
syntax region svString start=+"+ skip=+\\"+ end=+"+
syntax keyword svType real realtime event reg wire integer logic bit time byte chandle genvar signed unsigned shortint shortreal string void int specparam
syntax keyword svDirection input output inout ref
syntax keyword svStorageClass parameter localparam virtual var protected rand const static automatic extern forkjoin export import
syntax match svInvPre "`\(\K\k*\)*\>"
syntax match svPreProc "`\(__FILE__\|__LINE__\|begin_keywords\|celldefine\|default_nettype\|end_keywords\|endcelldefine\|include\|line\|nounconnected_drive\|pragma\|resetall\|timescale\|unconnected_drive\|undef\|undefineall\)\>"
syntax match svPreCondit "`\(else\|elsif\|endif\|ifdef\|ifndef\)\>"
syntax match svInclude "`include\>"
syntax match svDefine "`define\>"
syntax keyword svConditional if else iff
syntax match svLabel "^\W*[a-zA-Z_]\+[a-zA-Z_0-9,\[\]\t ]*:"he=e-1 contained
syntax region svCase matchgroup=svConditional start="\<case\|casex\|casez\>" end="\<endcase\>" contains=ALL
syntax keyword svRepeat for foreach do while forever repeat
syntax keyword svKeyword fork join join_any join_none begin end module endmodule function endfunction task endtask always always_ff always_latch always_comb initial this generate endgenerate config endconfig class endclass clocking endclocking interface endinterface module endmodule package endpackage modport posedge negedge edge defparam assign deassign alias return disable wait continue and buf bufif0 bufif1 nand nor not or xnor xor tri tri0 tri1 triand trior trireg pull0 pull1 pullup pulldown cmos default endprimitive endspecify endtable force highz0 highz1 ifnone large macromodule medium nmos notif0 notif1 pmos primitive rcmos release rnmos rpmos rtran rtranif0 rtranif1 scalared small specify strong0 strong1 supply0 supply1 table tran tranif0 tranif1 vectored wand weak0 weak1 wor cell design incdir liblist library noshowcancelled pulsestyle_ondetect pulsestyle_onevent showcancelled use instance uwire assert assume before bind bins binsof break constraint context cover covergroup coverpoint cross dist endgroup endprogram endproperty endsequence enum expect extends final first_match ignore_bins illegal_bins inside intersect local longint matches new null packed priority program property pure randc randcase randsequence sequence solve struct super tagged throughout timeprecision timeunit type typedef union unique wait_order wildcard with within accept_on checker endchecker eventually global implies let nexttime reject_on restrict s_always s_eventually s_nexttime s_until s_until_with strong sync_accept_on sync_reject_on unique0 until until_with untyped weak implements interconnect nettype soft
syntax match svNumber "\<[0-9ZzXx]\+\('\([Hh][0-9a-fA-FZzXx]*\|[Dd][0-9ZzXx]*\|[Bb][01XxZz]*\)\)\?\>"
syntax match svTime "\<[0-9]\+\(ns\|ms\|us\|fs\|ps\|s\)\>"
syntax keyword svStructure struct union enum
syntax keyword svTypedef typedef
syntax match svInvSystemFunction "\$\(\K\k*\)"
syntax match svSystemFunction "\$\(finish\|stop\|exit\|realtime\|stime\|time\|printtimescale\|timeformat\|bitstoreal\|realtobits\|bitstoshortreal\|shortrealtobits\|itor\|rtoi\|signed\|unsigned\|cast\|bits\|isunbounded\|typename\|unpacked_dimensions\|dimensions\|left\|right\|low\|high\|increment\|size\|clog2\|asin\|ln\|acos\|log10\|atan\|exp\|atan2\|sqrt\|hypot\|pow\|sinh\|floor\|cosh\|ceil\|tanh\|sin\|asinh\|cos\|acosh\|tan\|atanh\|countbits\|countones\|onehot\|onehot0\|isunknown\|fatal\|error\|warning\|info\|fatal\|error\|warning\|info\|asserton\|assertoff\|assertkill\|assertcontrol\|assertpasson\|assertpassoff\|assertfailon\|assertfailoff\|assertnonvacuouson\|assertvacuousoff\|sampled\|rose\|fell\|stable\|changed\|past\|past_gclk\|rose_gclk\|fell_gclk\|stable_gclk\|changed_gclk\|future_gclk\|rising_gclk\|falling_gclk\|steady_gclk\|changing_gclk\|coverage_control\|coverage_get_max\|coverage_get\|coverage_merge\|coverage_save\|get_coverage\|set_coverage_db_name\|load_coverage_db\|random\|urandom\|urandom_range\|dist_chi_square\|dist_erlang\|dist_exponential\|dist_normal\|dist_poisson\|dist_t\|dist_uniform\|q_initialize\|q_add\|q_remove\|q_full\|q_exam\|asyncandarray\|asyncandplane\|asyncnandarray\|asyncnandplane\|asyncorarray\|asyncorplane\|asyncnorarray\|asyncnorplane\|syncandarray\|syncandplane\|syncnandarray\|syncnandplane\|syncorarray\|syncorplane\|syncnorarray\|syncnorplane\|system\|contained\|transparent\)\>"
syntax match svObjectFunctions "\.\(num\|size\|delete\|exists\|first\|last\|next\|prev\|insert\|pop_front\|pop_back\|push_front\|push_back\|find\|find_index\|find_first\|find_first_index\|find_last\|find_last_index\|min\|max\|reverse\|sort\|rsort\|shuffle\|sum\|product\|and\|or\|xor\)\>\(\s\|\n\)*("he=e-1
syntax match svOperator "\(\~\|&\||\|\^\|=\|!\|?\|:\|@\|<\|>\|%\|+\|-\|\*\|\/[\/\*]\@!\)"
syntax match svDelimiter "\({\|}\|(\|)\)"

highlight! default link svTodo Todo
highlight! default link svLineComment Comment
highlight! default link svBlockComment Comment
highlight! default link svBoolean Boolean
highlight! default link svString String
highlight! default link svType Type
highlight! default link svDirection StorageClass
highlight! default link svStorageClass StorageClass
highlight! default link svPreProc PreProc
highlight! default link svPreCondit PreCondit
highlight! default link svInclude Include
highlight! default link svDefine Define
highlight! default link svMacro Macro
highlight! default link svConditional Conditional
highlight! default link svLabel Label
highlight! default link svRepeat Repeat
highlight! default link svKeyword Keyword
highlight! default link svNumber Number
highlight! default link svTime Number
highlight! default link svStructure Structure
highlight! default link svTypedef Typedef
highlight! default link svSystemFunction Function
highlight! default link svOperator Operator
highlight! default link svDelimiter Delimiter
highlight! default link svObjectFunctions Function

highlight! default link svFunction none
highlight! default link svCase none
highlight! default link svPreprocessor none
highlight! default link svSystemFunctionName none
highlight! default link svInvPre none
highlight! default link svInvSystemFunction none
