;; An Emacs/Magit utility for jumping from diffs in test.out files to
;; the corresponding test file.
;;
;; Instructions:
;;
;;   1. open emacs in the spark2014 directory
;;   2. M-x magit-status
;;   3. M-x load-file [this file]
;;
;; Then placing a cursor on a test.out line like the ones below and pressing
;; M-RET (i.e. Alt+Enter) will open buffer with a corresponding test file.
;;
;; modified   testsuite/gnatprove/tests/V808-020__flow_null/test.out
;; @@ -1,2 +1,2 @@
;; -nullparam.adb:1:22: warning: "Dummy" is not modified, could be IN
;; +nullparam.adb:1:22: warning: "Dummy" is not modified, could be OUT
;;  nullparam.adb:13:04: warning: statement has no effec

(require 'rx) ;; for human-readable regular expressions

(defun magit-visit-test-file ()
  (interactive)
  (save-excursion
    (progn
      (beginning-of-line)
      (when (looking-at
             (rx (and line-start
                      (any ? ?+ ?-)
                      (group (1+ (any "A-Za-z0-9_\-")) (or ".adb" ".ads"))
                      ;; ~ should be also allowed, e.g. a~b.ads
                      ":" (group (1+ digit))
                      ":" (group (1+ digit))
                      ": ")))

        (let ((diff-file (match-string-no-properties 1))
              (diff-line (string-to-number (match-string-no-properties 2)))
              (diff-coln (string-to-number (match-string-no-properties 3)))
              (test-out-path (magit-file-at-point)))
          (find-file
           (concat (file-name-directory test-out-path) diff-file))
          (goto-char (point-min))
          (forward-line (1- diff-line))
          (forward-char (1- diff-coln)))))))

(local-set-key (kbd "M-RET") 'magit-visit-test-file)
