"Author: Nachum Kanovsky
"Email: nkanovsky yahoo com
"Version: 1.3
if exists("b:did_ftplugin")
	finish
endif

let b:did_ftplugin = 1

augroup filetypedetect
	au! BufRead,BufNewFile *.v,*.vh,*.sv,*.svh setfiletype systemverilog
augroup END
