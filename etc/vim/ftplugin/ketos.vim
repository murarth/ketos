" Vim filetype plugin
" Language:    Ketos
" Maintainer:  Murarth <murarth@gmail.com>
" Last Change: December 27, 2015
" URL:         https://github.com/murarth/ketos

" Only do this when not done yet for this buffer
if exists("b:did_ftplugin")
  finish
endif

" Don't load another plugin for this buffer
let b:did_ftplugin = 1

setl comments=:;;;,:;;,:;,sr:#\|,mb:\|,ex:\|#
setl commentstring=;%s
setl define=^\\s*(def\\k*
setl formatoptions+=croql
setl iskeyword=33,36,37,38,42,43,45-57,60-63,65-90,94,95,97-122,124
setl lisp
setl lispwords+=define,macro
setl shiftwidth=2
setl tabstop=2

let b:undo_ftplugin = 'setlocal comments< commentstring< define< formatoptions< iskeyword< lisp< lispwords< shiftwidth< tabstop<'
