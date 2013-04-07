;;; spire-mode.el --- Spire major mode

;; URL: https://github.com/spire/spire/blob/master/editor/emacs/spire-mode.el
;; Copyright (C) 2013, Larry Diehl
;; Author: Larry Diehl
;; License: https://github.com/spire/spire/blob/master/LICENSE
;; Keywords: extensions

;; Commentary:
;; This mode uses generic mode
;; (http://www.emacswiki.org/emacs/GenericMode)
;; for syntax highlighting,
;; and comint mode
;; (http://emacswiki.org/emacs/ComintMode)
;; for interacting with processes.

(require 'generic-x)

(define-generic-mode 'spire-mode
  '("--") ;; comments
  '("in") ;; keywords
  '(("\\<\\(Unit\\|Bool\\|Type\\)\\>" . 'font-lock-type-face) ;; types
    ("\\<\\(if\\|then\\|else\\|caseBool\\|\\$\\)\\>" . 'font-lock-builtin-face) ;; builtins
    ("\\<\\(tt\\|true\\|false\\)\\>" . 'font-lock-constant-face) ;; constants
    )
  '("\\.spire$")                      ;; files for which to activate this mode
  nil                               ;; other functions to call
  "A simple mode for roy files"     ;; doc string for this mode
  )

(defcustom spire-command "spire"
  "The Spire command used for type checking. Must be in your $PATH."
  :type 'string
  :group 'spire)

(provide 'spire-mode)
