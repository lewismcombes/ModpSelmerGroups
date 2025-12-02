# ~/.profile: executed by bash(1) for login shells including interactive ones
# BEWARE: other Bourne-shell types e.g. /bin/sh also run ~/.profile,
# but they may not like ~/bashrc or bash-specific syntax.
if [ "$BASH" ]; then
 if [ "$PS1" ]; then
  if [ -r ~/.bashrc ]; then
    . ~/.bashrc
  fi
 fi
else
  if [ -r ~/.myenv ]; then
    . ~/.myenv
  fi
fi
