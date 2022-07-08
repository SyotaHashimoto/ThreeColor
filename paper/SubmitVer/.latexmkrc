#!/usr/bin/env perl

# Path
$ENV{'TEXINPUTS'} = '.:..:/home/kmr/Dropbox/settings/tex//:' .
$ENV{'TEXINPUTS'};

# LaTeX
# -halt-on-error: 最初のエラーが起きた時点で処理を止める (参照ファイルがないときは聞いてくる)
# -interaction=...
#   nonstopmode: エラーに出会ってもそのまま進むが，参照ファイルがないときはそこで処理を止める．
#   scrollmode: エラーに出会ってもそのまま進むが，参照ファイルがないときはそこで処理を止めて聞いてくる．
#   batchmode: ほぼ無言．エラーも成功も表示されない．
#   errorstopmode: エラーに出会うと聞いてくる
# -synctex=1: synctex を有効にする．ビューアーからエディタにジャンプできる
#$latex = 'uplatex -synctex=1 -halt-on-error -interaction=batchmode -file-line-error %O %S';
$latex = 'platex -synctex=1 -halt-on-error -interaction=nonstopmode';

$max_repeat = 5;

# BibTeX
$bibtex = 'pbibtex %O %S';
$biber = 'biber --bblencoding=utf8 -u -U --output_safechars %O %S';

# index
$makeindex = 'mendex %O -o %D %S';

# DVI / PDF
# pdf_mode = ?
#   0: pdf化しない場合
#   1: pdflatexを使う場合
#   2: ps2pdfを使う場合
#   3: tex->dvi->pdf
$pdf_mode = 3;

#$dvipdf = 'dvipdfmx -f cid-x.map %O -o %D %S';
$dvipdf = 'dvipdfmx %O -o %D %S';

# preview
$pvc_view_file_via_temporary = 0;
if ($^O eq 'linux') {
    $dvi_previewer = "xdg-open %S";
    $pdf_previewer = "xdg-open %S";
} elsif ($^O eq 'darwin') {
    $dvi_previewer = "open %S";
    $pdf_previewer = "open %S";
} else {
    $dvi_previewer = "start %S";
    $pdf_previewer = "start %S";
}

# clean up
$clean_full_ext = "%R.synctex.gz"
