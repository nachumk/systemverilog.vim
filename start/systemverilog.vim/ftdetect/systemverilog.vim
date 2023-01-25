"Author: Nachum Kanovsky
"Email: nkanovsky@yahoo.com
"Version: 1.15

augroup filetypedetect
	au! BufRead,BufNewFile *.v,*.vh,*.sv,*.svh,*.svp,*.svi setfiletype systemverilog
augroup END
