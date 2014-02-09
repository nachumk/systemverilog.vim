"Author: Nachum Kanovsky
"Email: nkanovsky yahoo com
"Version: 1.3
if exists("b:did_indent")
	finish
endif

let b:did_indent = 1

setlocal indentexpr=GetSystemVerilogIndent(v:lnum)
setlocal indentkeys&
setlocal indentkeys+==begin,=case,=if,=fork,=else,=end,=join,(,),{,},;

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

"b - 'begin', '(', '{'
"e - 'end', ')', '{'
"f - 'class', 'function', 'task'
"h - 'endclass', 'endfunction', 'endtask'
"l - '//' -- at start of line
"s - '/*' -- start comment
"p - '*/' -- stop comment
"x - 'if', 'else', 'for', 'do, 'while', 'always', 'initial', -- execution commands
"c - 'pure'
function! s:ConvertToCodes( codeline )
	" keywords that don't affect indent: module endmodule package endpackage interface endinterface
	let delims = substitute(a:codeline, "\\<\\(\\%(initial\\|always\\|always_comb\\|always_ff\\|always_latch\\|final\\|begin\\|if\\|for\\|foreach\\|do\\|while\\|forever\\|repeat\\|case\\|fork\\|ifdef\\|else\\|end\\|endif\\|endcase\\|join\\|join_any\\|join_none\\|class\\|config\\|clocking\\|function\\|task\\|specify\\|covergroup\\|pure\\|assume\\|assert\\|cover\\|endclass\\|endconfig\\|endclocking\\|endfunction\\|endtask\\|endspecify\\|endgroup\\|property\\|endproperty\\|sequence\\|checker\\|endsequence\\|endchecker\\)\\>\\)\\@!\\k\\+", "", "g")
	let delims = substitute(delims, "^\\s*\\/\\/.*$", "l", "g") " convert line comments and keep them b/c comments should not calculate new indent
	let delims = substitute(delims, "\\/\\/.*", "", "g") " remove line comments after text (indentation based on text not comment)
	let delims = substitute(delims, "\".*\"", "", "g") " remove strings
	let delims = substitute(delims, "\\/\\*", "s", "g") " convert block comment start
	let delims = substitute(delims, "\\*\\/", "p", "g") " convert block comment end
	let delims = substitute(delims, "\\[[^:\\[\\]]*:[^:\\[\\]]*\\]", "", "g") "remove ranges
	let delims = substitute(delims, "\\(`\\<if\\>\\|`\\<ifdef\\>\\)", "b", "g")
	let delims = substitute(delims, "\\(`\\<endif\\>\\)", "e", "g")
	let delims = substitute(delims, "\\(`\\<else\\>\\)", "eb", "g")
	let delims = substitute(delims, "\\<\\(begin\\|case\\|fork\\)\\>", "b", "g")
	let delims = substitute(delims, "\\<\\(end\\|endcase\\|join\\|join_any\\|join_none\\)\\>", "e", "g")
	let delims = substitute(delims, "\\<\\(class\\|config\\|clocking\\|function\\|task\\|specify\\|covergroup\\|property\\|sequence\\|checker\\)\\>", "f", "g")
		let delims = substitute(delims, "\\<\\(endclass\\|endconfig\\|endclocking\\|endfunction\\|endtask\\|endspecify\\|endgroup\\|endproperty\\|endsequence\\|endchecker\\)\\>", "h", "g")
	let delims = substitute(delims, "\\<\\(if\\|else\\|for\\|foreach\\|do\\|while\\|forever\\|repeat\\|always\\|always_comb\\|always_ff\\|always_latch\\|initial\\)\\>", "x", "g")
	let delims = substitute(delims, "\\<\\(pure\\|assume\\|assert\\|cover\\)\\>", "c", "g")
	" convert (, ), only after whole word conversions are done
	let delims = substitute(delims, "[({]", "b", "g") " convert ( to indicate start of indent
	let delims = substitute(delims, "[)}]", "e", "g") " convert ) to indicate end of indent
	let delims = substitute(delims, "^\s*`.*", "", "g") " remove other preprocessor commands
	let delims = substitute(delims, "[/@<=#,.]*", "", "g") "remove extraneous characters
	let delims = substitute(delims, "\\s", "", "g") " remove whitespace
	let delims = substitute(delims, "^:", "x", "g") " convert case branch (first on line)
	let delims = substitute(delims, ":", "", "g") " remove labels
	let delims = substitute(delims, "x\\+", "x", "g") " consolidate x
	while (match(delims, "\\(b[^be]*e\\)") != -1)
		let delims = substitute(delims, "\\(b[^be]*e\\)", "", "g") "remove any begin end pairs
	endwhile
	while (match(delims, "\\(s[^sp]*p\\)") != -1)
		let delims = substitute(delims, "\\(s[^sp]*p\\)", "", "g") "remove any comment start stop pairs
	endwhile
	let delims = substitute(delims, "cf", "", "g")
	return delims
endfunction

function! s:GetPrevNonCommentLineNum( line_num )
	let nline = a:line_num
	let in_comment = 0
	while nline > 0
		let nline = prevnonblank( nline-1 )
		let this_codeline = getline( nline )
		let this_codes = s:ConvertToCodes( this_codeline )
		if this_codes =~ s:LINE_COMMENT
			continue
		endif
		if this_codes =~ s:BLOCK_COMMENT_STOP
			let in_comment = 1
		endif
		if !in_comment
			break
		endif
		if this_codes =~ s:BLOCK_COMMENT_START
			let in_comment = 0
		endif
	endwhile
	return nline
endfunction

let b:in_block_comment = 0

"Intending to handle block comment by seeing /* and forward reading till end to find */ and then storing a buffer local variable indicating last line of block comment, and b:changedtick (change number which always increments). Using that variable I can ignore normal indentation until I get there.
function! GetSystemVerilogIndent( line_num )
	let this_codeline = getline( a:line_num )
	let this_codes = s:ConvertToCodes( this_codeline )

"	echo (this_codes)
"	return -1

	if this_codes =~ s:BLOCK_COMMENT_STOP || b:block_comment_change != b:changedtick || b:block_comment_line != a:line_num - 1
		let b:in_block_comment = 0
	endif
	if this_codes =~ s:BLOCK_COMMENT_STOP
		return -1
	endif
	if this_codes =~ s:BLOCK_COMMENT_START || b:in_block_comment
		let b:in_block_comment = 1
		let b:block_comment_line = a:line_num
		let b:block_comment_change = b:changedtick
		return -1
	endif

	if (this_codes =~ s:LINE_COMMENT)
		return -1
	endif

	" Line 1 always goes at column 0
	if a:line_num == 1
		return 0
	endif

	let prev1_codeline_num = s:GetPrevNonCommentLineNum( a:line_num )
	let prev1_codeline = getline( prev1_codeline_num )
	let prev1_codes = s:ConvertToCodes( prev1_codeline )

	if prev1_codeline_num == 0
		let indnt = 0
	else
		let indnt = indent( prev1_codeline_num )
	endif

	let prev2_codeline_num = s:GetPrevNonCommentLineNum( prev1_codeline_num )
	let prev2_codeline = getline( prev2_codeline_num )
	let prev2_codes = s:ConvertToCodes( prev2_codeline )

	if prev2_codes =~ s:LINE_INDENT && prev1_codes =~ s:EXEC_LINE " used up single indent in previous line, return back to normal indent
		let indnt = indnt - &shiftwidth
	endif

	if prev1_codes =~ s:GROUP_INDENT_START
		let indnt = indnt + &shiftwidth
	endif

	if this_codes =~ s:GROUP_INDENT_STOP
		return indnt - &shiftwidth
	endif

	if prev1_codes =~ s:BLOCK_INDENT_START
		let indnt = indnt + &shiftwidth
	endif
	if this_codes =~ s:BLOCK_INDENT_STOP
		return indnt - &shiftwidth
	endif

	if prev1_codes =~ s:LINE_INDENT
		let indnt = indnt + &shiftwidth
		if this_codes =~ s:LINE_INDENT || this_codes =~ s:BLOCK_INDENT_START
			let indnt = indnt - &shiftwidth
		endif
	endif

	return indnt
endfunction
