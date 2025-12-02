# ~/.bashrc: executed by bash(1) for non-login shells.

# Set PATH and other environment variables:
[[ -r ~/.myenv ]] && . ~/.myenv

umask 027

# Set prompt:
#PS1='\h:\w\$ '
PS1='\w\$ '

# Aliases:
alias ll='ls -l'
