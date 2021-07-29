"Author: Nachum Kanovsky
"Email: nkanovsky@yahoo.com
"Version: 1.12
if exists("b:did_ftplugin")
	finish
endif

let b:did_ftplugin = 1

" Undo the plugin effect
"let b:undo_ftplugin = "unlet b:match_ignorecase b:match_words"

" Let the matchit plugin know what items can be matched.
if exists("loaded_matchit")
  let b:match_ignorecase=0
  let b:match_words=
        \ '\<begin\>:\<end\>,' .
        \ '\<if\>\|\<assert\>:\(`\s*\)\@<!else\>,' .
        \ '\<module\>:\<endmodule\>,' .
        \ '\<class\>:\<endclass\>,' .
        \ '\<program\>:\<endprogram\>,' .
        \ '\<clocking\>:\<endclocking\>,' .
        \ '\<property\>:\<endproperty\>,' .
        \ '\<sequence\>:\<endsequence\>,' .
        \ '\<package\>:\<endpackage\>,' .
        \ '\<covergroup\>:\<endgroup\>,' .
        \ '\<primitive\>:\<endprimitive\>,' .
        \ '\<specify\>:\<endspecify\>,' .
        \ '\<generate\>:\<endgenerate\>,' .
        \ '\<interface\>\(\s\+\<\k\+\>\s*[(#]\)\@=:\<endinterface\>,' .
        \ '\<function\>:\<endfunction\>,' .
        \ '\<task\>:\<endtask\>,' .
        \ '\<case\>\|\<casex\>\|\<casez\>:\<endcase\>,' .
        \ '\<\(\(disable\|wait\)\s\+\)\@<!fork\>:\<join\>\|\<join_any\>\|\<join_none\>,' .
        \ '\<ifdef\>:\(`\s*\)\@<=else\>:\<endif\>,' .
        \ '\<generate\>:\<endgenerate\>'
endif
