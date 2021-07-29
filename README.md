systemverilog.vim
=================

SystemVerilog indent and syntax scripts

### VIM 8 Install:

Install by cloning repository:

    git clone git://github.com/nachumk/systemverilog.vim ~/.vim/pack/systemverilog.vim

### VIM 7 Install:

VIM 7 doesn't have a native package management system. Using pathogen is recommended.

Pathogen Install (will enable VIM 8's directory structure of 'pack' instead of 'bundle' in VIM 7 - make sure Pathogen is updated as well)

https://github.com/tpope/vim-pathogen

Install by cloning repository:

    git clone git://github.com/nachumk/systemverilog.vim ~/.vim/pack/systemverilog.vim

### My .vimrc:

    "Enable matchit
    runtime macros/matchit.vim
    if v:version < 800
        "Start pathogen
        execute pathogen#infect()
    endif
    "Turn on syntax highlighting
    syntax on
    "Enable filetype detection
    filetype plugin indent on
    "Enable folding based on indent (on 8.0 and greater versions)
    if v:version >= 800
        set foldmethod=indent
        set foldnestmax=10
        set nofoldenable
        set foldlevelstart=10
    endif
