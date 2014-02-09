"Author: Nachum Kanovsky
"Email: nkanovsky yahoo com
"Version: 0.5
if exists("b:did_ftplugin")
	finish
endif
augroup filetypedetect
	au! BufRead,BufNewFile *.v,*.vh,*.sv,*.svh setfiletype systemverilog
augroup END
