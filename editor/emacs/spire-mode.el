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
(require 'comint)

(defun spire-bind-keys ()
  (global-set-key (kbd "C-c C-l") 'spire-check-file)
  )

(define-generic-mode 'spire-mode
  '("--") ;; comments
  '("in") ;; keywords
  '(("\\<\\(Unit\\|Bool\\|Type\\)\\>" . 'font-lock-type-face) ;; types
    ("\\<\\(if\\|then\\|else\\|caseBool\\|\\$\\)\\>" . 'font-lock-builtin-face) ;; builtins
    ("\\<\\(tt\\|true\\|false\\)\\>" . 'font-lock-constant-face) ;; constants
    )
  '("\\.spire$") ;; file extension
  (list 'spire-bind-keys) ;; other functions to call
  "A mode for Spire programs." ;; doc string
  )

(defconst *spire* "*Spire*"
  "Buffer used by Spire")

(defcustom spire-command "spire"
  "The Spire command used for type checking. Must be in your $PATH."
  :type 'string
  :group 'spire)

(defun spire-check-file ()
  "Type check a file using `spire-command' as an inferior mode."
  (interactive)
  (when (get-buffer *spire*)
    (with-current-buffer *spire*
      (when (comint-check-proc *spire*)
        (comint-kill-subjob))
      (delete-region (point-min) (point-max))
      )
    )

  (apply 'make-comint "Spire" spire-command nil
         (list (buffer-file-name))
         )
  (display-buffer *spire*)
  )

(provide 'spire-mode)