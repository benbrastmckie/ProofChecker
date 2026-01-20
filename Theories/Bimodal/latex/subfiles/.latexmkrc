# Subfiles latexmkrc - adds parent assets to TEXINPUTS
$ENV{'TEXINPUTS'} = '../assets/:' . ($ENV{'TEXINPUTS'} || '');

# Inherit parent latexmk configuration
do '../latexmkrc';
