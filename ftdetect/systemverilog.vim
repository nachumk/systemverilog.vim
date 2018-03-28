"Author: Nachum Kanovsky
"Email: nkanovsky yahoo com
"Version: 1.7

augroup filetypedetect
	au! BufRead,BufNewFile *.v,*.vh,*.sv,*.svh setfiletype systemverilog
augroup END
