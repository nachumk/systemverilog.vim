systemverilog.vim
=================

SystemVerilog indent and syntax scripts

Pathogen Install
----------------

Pathogen is supported by putting the systemverilog.vim folder under the bundle directory.

https://github.com/tpope/vim-pathogen

### Install by cloning repository:

    git clone git://github.com/nachumk/systemverilog.vim ~/.vim/bundle/systemverilog.vim

My .vimrc:

    "Enable matchit
    runtime macros/matchit.vim
    "Start pathogen
    execute pathogen#infect()
    "Turn on syntax highlighting
    syntax on
    "Enable filetype detection
    filetype plugin indent on
    "Enable folding based on indent
    set foldmethod=indent
    set foldnestmax=10
    set nofoldenable
    set foldlevelstart=10
