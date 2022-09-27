"Author: Nachum Kanovsky
"Email: nkanovsky@yahoo.com
"Version: 1.14
"URL: https://github.com/nachumk/systemverilog.vim
if exists("b:did_indent")
	finish
endif

let b:did_indent = 1

setlocal indentexpr=GetSystemVerilogIndent(v:lnum)
setlocal indentkeys&
setlocal indentkeys+==end,=join,(,),{,},=`begin_keywords,=`celldefine,=`default_nettype,=`define,=`end_keywords,=`endcelldefine,=`endif,=`ifdef,=`ifndef,=`include,=`nounconnected_drive,=`pragma,=`resetall,=`timescale,=`unconnected_drive,=`undef,=`undefineall;

if exists("*GetSystemVerilogIndent")
	finish
endif

let s:BLOCK_COMMENT_START = '^s.*$'
let s:BLOCK_COMMENT_STOP = '^.*p$'
let s:LINE_COMMENT = '^l$'
let s:GROUP_INDENT_START = 'f'
let s:GROUP_INDENT_STOP = 'h'
let s:BLOCK_INDENT_START = 'b'
let s:BLOCK_INDENT_STOP = 'e'
let s:LINE_INDENT = '^.*x$'
let s:EXEC_LINE = '^.*;$'
let s:PREPROCESSOR = '^z.*$'

"b - 'begin', '(', '{'
"e - 'end', ')', '{'
"f - 'class', 'function', 'task'
"h - 'endclass', 'endfunction', 'endtask'
"l - '//' -- at start of line
"s - '/*' -- start comment
"p - '*/' -- stop comment
"x - 'if', 'else', 'for', 'do, 'while', 'always', 'initial', -- execution commands
function! s:ConvertToCodes( codeline )
	" keywords that don't affect indent: module endmodule package endpackage interface endinterface
	let delims = substitute(a:codeline, '\<virtual\>', '', 'g') " remove keyword virtual - helps for pure <virtual> function/task
	let delims = substitute(a:codeline, '\<\(\%(initial\|always\|always_comb\|always_ff\|always_latch\|final\|begin\|disable\|if\|extern\|for\|foreach\|do\|while\|forever\|repeat\|randcase\|case\|casex\|casez\|wait\|fork\|ifdef\|ifndef\|else\|end\|endif\|begin_keywords\|celldefine\|default_nettype\|define\|end_keywords\|endcelldefine\|include\|nounconnected_drive\|pragma\|resetall\|timescale\|unconnected_drive\|undef\|undefineall\|endcase\|join\|join_any\|join_none\|class\|config\|clocking\|function\|task\|specify\|covergroup\|pure\|endclass\|endconfig\|endclocking\|endfunction\|endtask\|endspecify\|endgroup\|assume\|assert\|cover\|property\|typedef\|endproperty\|sequence\|checker\|endsequence\|endchecker\)\>\)\@!\k\+', '', 'g')
	let delims = substitute(delims, 'wait\s\+fork', '', 'g') " remove wait fork
	let delims = substitute(delims, 'disable\s\+fork', '', 'g') " remove disable fork
	let delims = substitute(delims, 'pure\s\+function', '', 'g') " remove pure function
	let delims = substitute(delims, 'extern\s\+function', '', 'g') " remove extern function
	let delims = substitute(delims, 'pure\s\+task', '', 'g') " remove pure task
	let delims = substitute(delims, 'extern\s\+task', '', 'g') " remove extern task
	let delims = substitute(delims, 'typedef\s\+class', '', 'g') " remove typedef class
	let delims = substitute(delims, 'typedef', '', 'g') " remove typedef
	let delims = substitute(delims, 'assert\s\+property', '', 'g') " remove assert property
	let delims = substitute(delims, 'assume\s\+property', '', 'g') " remove assume property
	let delims = substitute(delims, 'cover\s\+property', '', 'g') " remove cover property
    let delims = substitute(delims, '`\s*\<\(begin_keywords\|celldefine\|default_nettype\|define\|else\|end_keywords\|endcelldefine\|endif\|ifdef\|ifndef\|include\|nounconnected_drive\|pragma\|resetall\|timescale\|unconnected_drive\|undef\|undefineall\)\>', 'z', 'g')
	let delims = substitute(delims, '\<\(begin\|randcase\|case\|casex\|casez\|fork\)\>', 'b', 'g')
	let delims = substitute(delims, '\<\(end\|endcase\|join\|join_any\|join_none\)\>', 'e', 'g')
	let delims = substitute(delims, '\<\(class\|config\|clocking\|function\|task\|specify\|covergroup\|property\|sequence\|checker\)\>', 'f', 'g')
	let delims = substitute(delims, '\<\(endclass\|endconfig\|endclocking\|endfunction\|endtask\|endspecify\|endgroup\|endproperty\|endsequence\|endchecker\)\>', 'h', 'g')
	let delims = substitute(delims, '\<\(if\|else\|assert\|for\|foreach\|do\|while\|forever\|repeat\|always\|always_comb\|always_ff\|always_latch\|initial\)\>', 'x', 'g')
	let delims = substitute(delims, '^\s*\/\/.*$', 'l', 'g') " convert line comments and keep them b/c comments should not calculate new indent
	let delims = substitute(delims, '\/\/.*', '', 'g') " remove line comments after text (indentation based on text not comment)
	let delims = substitute(delims, '\".\{-}\(\\\)\@<!\"', '', 'g') " remove strings
	let delims = substitute(delims, '\/\*', 's', 'g') " convert block comment start
	let delims = substitute(delims, '\*\/', 'p', 'g') " convert block comment end
	let delims = substitute(delims, '\[[^:\[\]]*:[^:\[\]]*\]', '', 'g') "remove ranges
	let delims = substitute(delims, '\@', 'x', 'g')
	" convert (, ), only after whole word conversions are done
	let delims = substitute(delims, '[({]', 'b', 'g') " convert ( to indicate start of indent
	let delims = substitute(delims, '[)}]', 'e', 'g') " convert ) to indicate end of indent
	let delims = substitute(delims, '^\s*`.*', '', 'g') " remove other preprocessor commands
	let delims = substitute(delims, '[/@<=#,.]*', '', 'g') "remove extraneous characters
	let delims = substitute(delims, '\s', '', 'g') " remove whitespace
	let delims = substitute(delims, '^o\+:', 'x', 'g') " convert case branch (first on line)
	let delims = substitute(delims, ':', '', 'g') " remove labels
	let delims = substitute(delims, 'x\+', 'x', 'g') " consolidate x
	let delims = substitute(delims, 'o\+', 'o', 'g') " consolidate o
	while (match(delims, '\(b[^be]*e\)') != -1)
		let delims = substitute(delims, '\(b[^be]*e\)', '', 'g') "remove any begin end pairs
	endwhile
	while (match(delims, '\(f[^fh]*h\)') != -1)
		let delims = substitute(delims, '\(f[^fh]*h\)', '', 'g') "remove any function endfunction pairs
	endwhile
	while (match(delims, '\(s[^sp]*p\)') != -1)
		let delims = substitute(delims, '\(s[^sp]*p\)', '', 'g') "remove any comment start stop pairs
	endwhile
	return delims
endfunction

function! s:GetPrevWholeLineNum ( line_num )
	let prev1_line_num = prevnonblank( a:line_num - 1)
	let prev2_line_num = prev1_line_num - 1
	let prev2_codeline = getline( prev2_line_num )
	while ( strpart( prev2_codeline , strlen(prev2_codeline) - 1 , 1) == '\' )
		let prev1_line_num = prev1_line_num - 1
		let prev2_line_num = prev1_line_num - 1
		let prev2_codeline = getline( prev2_line_num )
	endwhile

	return prev1_line_num
endfunction

function! s:GetWholeLine ( line_num )
	let line_num = a:line_num
	let codeline = getline( line_num )
	while ( strpart( codeline , strlen(codeline) - 1 , 1) == '\' )
		let line_num = line_num + 1
		let codeline = strpart( codeline , 0 , strlen( codeline ) - 2 ) . " " . getline (line_num)
	endwhile

	return codeline
endfunction

function! s:GetCodeIndent ( indnt, prev2_codes, prev1_codes, this_codes )
	let indnt = a:indnt
	if a:prev2_codes =~ s:LINE_INDENT && a:prev1_codes =~ s:EXEC_LINE " used up single indent in previous line, return back to normal indent
		let indnt = indnt - &shiftwidth
	endif

	if a:prev1_codes =~ s:GROUP_INDENT_START
		let indnt = indnt + &shiftwidth
	endif

	if a:this_codes =~ s:GROUP_INDENT_STOP
		return indnt - &shiftwidth
	endif

	if a:prev1_codes =~ s:BLOCK_INDENT_START
		let indnt = indnt + &shiftwidth
	endif
	if a:this_codes =~ s:BLOCK_INDENT_STOP
		return indnt - &shiftwidth
	endif

	if a:prev1_codes =~ s:LINE_INDENT
		let indnt = indnt + &shiftwidth
		if a:this_codes =~ s:LINE_INDENT || a:this_codes =~ s:BLOCK_INDENT_START
			let indnt = indnt - &shiftwidth
		endif
	endif

	return indnt
endfunction

let b:in_block_comment = 0

"Intending to handle block comment by seeing /* and forward reading till end to find */ and then storing a buffer local variable indicating last line of block comment, and b:changedtick (change number which always increments). Using that variable I can ignore normal indentation until I get there.
function! GetSystemVerilogIndent( line_num )
	if a:line_num == 1
		return 0
	endif

	let this_codeline = getline( a:line_num )
	let prev1_line_num = prevnonblank( a:line_num - 1)
	let prev1_codeline = getline( prev1_line_num )
	let prev2_line_num = prev1_line_num - 1
	let prev2_codeline = getline( prev2_line_num )

	let indnt = indent( prev1_line_num )

	" Check for line continuations ( line ends with backslash )
	if ( strpart( prev1_codeline , strlen(prev1_codeline) - 1 , 1) == '\' )
		if ( strpart( prev2_codeline , strlen(prev2_codeline) - 1 , 1) == '\' )
			return indnt
		else
			return indnt + &shiftwidth
		endif
	else
		if ( strpart( prev2_codeline , strlen(prev2_codeline) - 1 , 1) == '\' )
			let indnt = indnt - &shiftwidth
		endif
	endif

	let prev1_line_num = s:GetPrevWholeLineNum (a:line_num)
	let prev1_for_comment_line = prev1_line_num
	let prev1_codeline = s:GetWholeLine (prev1_line_num)
	let prev1_codes = s:ConvertToCodes(prev1_codeline)
	let in_comment = 0
	while ( prev1_codes =~ s:LINE_COMMENT || in_comment || prev1_codes =~ s:BLOCK_COMMENT_STOP || prev1_codes =~ s:BLOCK_COMMENT_START || prev1_codes =~ s:PREPROCESSOR)
		if (prev1_codes =~ s:BLOCK_COMMENT_STOP)
			let in_comment = 1
		endif
		if (prev1_codes =~ s:BLOCK_COMMENT_START)
			let in_comment = 0
		endif
		let prev1_line_num = s:GetPrevWholeLineNum (prev1_line_num)
		let prev1_codeline = s:GetWholeLine (prev1_line_num)
		let prev1_codes = s:ConvertToCodes(prev1_codeline)
	endwhile

	let prev2_line_num = s:GetPrevWholeLineNum (prev1_line_num)
	let prev2_codeline = s:GetWholeLine (prev2_line_num)
	let prev2_codes = s:ConvertToCodes(prev2_codeline)
	let in_comment = 0
	while ( prev2_codes =~ s:LINE_COMMENT || in_comment || prev2_codes =~ s:BLOCK_COMMENT_STOP || prev2_codes =~ s:BLOCK_COMMENT_START || prev2_codes =~ s:PREPROCESSOR)
		if (prev2_codes =~ s:BLOCK_COMMENT_STOP)
			let in_comment = 1
		endif
		if (prev2_codes =~ s:BLOCK_COMMENT_START)
			let in_comment = 0
		endif
		let prev2_line_num = s:GetPrevWholeLineNum (prev2_line_num)
		let prev2_codeline = s:GetWholeLine (prev2_line_num)
		let prev2_codes = s:ConvertToCodes(prev2_codeline)
	endwhile

	let this_codes = s:ConvertToCodes( this_codeline )

	let indnt = indent( prev1_line_num )

	let indnt = s:GetCodeIndent ( indnt, prev2_codes, prev1_codes, this_codes)

	if this_codes =~ s:BLOCK_COMMENT_STOP || b:block_comment_change != b:changedtick || b:block_comment_line != prev1_for_comment_line
		let b:in_block_comment = 0
	endif
	if this_codes =~ s:BLOCK_COMMENT_STOP
		return indent (a:line_num) + b:extra_block_indent
	endif
	if this_codes =~ s:BLOCK_COMMENT_START
		let b:in_block_comment = 1
		let b:block_comment_line = a:line_num
		let b:block_comment_change = b:changedtick
		let b:extra_block_indent = indnt - indent ( a:line_num )
		return indnt
	endif
	if b:in_block_comment
		let b:block_comment_line = a:line_num
		return indent (a:line_num) + b:extra_block_indent
	endif

	if (this_codes =~ s:PREPROCESSOR)
		return 0
	endif
	if (this_codes =~ s:LINE_COMMENT)
		return indnt
	endif

	return indnt
endfunction
