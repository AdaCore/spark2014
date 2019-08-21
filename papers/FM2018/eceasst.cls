% *************************************************************
% * Class file for the Electronic Communications of the EASST *
% *************************************************************
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{eceasst}[2009/07/08 ECEASST document class v1.6]
% Derived from the article class, fixing it to be two-sided 11pt output
% on A4 paper
\LoadClass[a4paper,11pt,twoside]{article}
% =======
% Lengths
% =======
\setlength{\textwidth}{420pt}
\setlength{\headheight}{35pt}
\setlength{\oddsidemargin}{16pt}
\setlength{\evensidemargin}{16pt}
\setlength{\parindent}{1em}
\setlength{\parskip}{0pt}
% =========
% Footnotes
% =========
\renewcommand{\@makefntext}[1]{%
  \noindent$^{\@thefnmark}$ #1}
% ====================================
% Spacing of figure and table captions
% ====================================
\setlength{\abovecaptionskip}{6pt}
\setlength{\belowcaptionskip}{6pt}
% ================================
% Environment for acknowledgements
% ================================
\newenvironment{acknowledge}{%
  \par\vspace{11pt}%
  \noindent\textbf{Acknowledgements:}\enspace}{%
  \par\vspace{11pt}}
% =============================
% Miscellaneous package imports
% =============================
\RequirePackage{mathptmx}
\RequirePackage[scaled=.90]{helvet}
\RequirePackage{courier}
% Graphics
\RequirePackage{graphicx}
% Colors
\RequirePackage{color}
\definecolor{easstblue}{rgb}{.05,.32,.66}
% ======================
% Package for Hyperlinks
% ======================
% Hyperlinks are coloured in easstblue
\RequirePackage[colorlinks=true,linkcolor=easstblue,citecolor=easstblue,filecolor=easstblue,menucolor=easstblue,urlcolor=easstblue,pdfpagemode={UseNone},pdfsubject={Software Science and Technology},pdfstartview={FitH}]{hyperref}
% URLs should be in normal font
\urlstyle{same}
% Command for emails
\newcommand{\email}[1]{\href{mailto:#1}{#1}}
% Command for Digital Object Identifiers
\newcommand{\doi}[1]{\href{http://dx.doi.org/#1}{doi:#1}}
% Correct anchors for figures and tables to be above the float
% ------------------------------------------------------------
\RequirePackage[all]{hypcap}
% =========================================
% AMS packages for mathematics and theorems
% =========================================
\RequirePackage[tbtags,sumlimits,intlimits,namelimits,reqno,fleqn]{amsmath}
\RequirePackage{amsthm}
\RequirePackage{amsfonts}
\RequirePackage{amssymb}
% Custom theorem-like environments
\newtheoremstyle{ectheorem}{11pt}{11pt}{\itshape}{}{\bfseries}{}{1em}{}
\newtheoremstyle{ecdefinition}{11pt}{11pt}{\upshape}{}{\bfseries}{}{1em}{}
\newtheoremstyle{ecremark}{11pt}{11pt}{\slshape}{}{\itshape}{}{1em}{}
\theoremstyle{ectheorem}
\newtheorem{theorem}{Theorem}
\newtheorem{proposition}{Proposition}
\newtheorem{lemma}{Lemma}
\newtheorem{corollary}{Corollary}
\theoremstyle{ecdefinition}
\newtheorem{definition}{Definition}
\newtheorem{algorithm}{Algorithm}
\theoremstyle{ecremark}
\newtheorem{remark}{Remark}
\newtheorem{example}{Example}
% =========================
% Names to use in \autorefs
% =========================
% Names for sections and similar:
\renewcommand{\partautorefname}{Part}
\renewcommand{\sectionautorefname}{Section}
\renewcommand{\subsectionautorefname}{Subsection}
\renewcommand{\subsubsectionautorefname}{Subsubsection}
% Names for theorem-like environments:
\renewcommand{\theoremautorefname}{Theorem}
\newcommand{\propositionautorefname}{Proposition}
\newcommand{\lemmaautorefname}{Lemma}
\newcommand{\corollaryautorefname}{Corollary}
\newcommand{\definitionautorefname}{Definition}
\newcommand{\algorithmautorefname}{Algorithm}
\newcommand{\exampleautorefname}{Example}
\newcommand{\remarkautorefname}{Remark}
% Names for figures and tables:
\renewcommand{\figureautorefname}{Figure}
\newcommand{\subfigureautorefname}{Figure}
\renewcommand{\tableautorefname}{Table}
\newcommand{\subtableautorefname}{Table}
% Name for the bibliography
\renewcommand{\refname}{Bibliography}
% ====================
% Frontmatter commands
% ====================
% The volume number and title
\newcommand{\ecvolnumber}{No \texttt{$\backslash$volume} defined!}
\newcommand{\volume}[2]{\renewcommand{\ecvolnumber}{Volume #1 (#2)}}
\newcommand{\ecvoltitle}{No \texttt{$\backslash$volumetitle} defined!}
\newcommand{\volumetitle}[1]{\renewcommand{\ecvoltitle}{#1}}
\newcommand{\ecvolshort}{\ecvolnumber}
\newcommand{\volumeshort}[1]{\renewcommand{\ecvolshort}{#1}}
% The volume or guest editors
\newcommand{\eceditor}{No \texttt{$\backslash$*ed(s)} defined!}
\newcommand{\voled}[1]{\renewcommand{\eceditor}{Volume Editor: #1}}
\newcommand{\voleds}[1]{\renewcommand{\eceditor}{Volume Editors: #1}}
\newcommand{\guested}[1]{\renewcommand{\eceditor}{Guest Editor: #1}}
\newcommand{\guesteds}[1]{\renewcommand{\eceditor}{Guest Editors: #1}}
% Title
\newcommand{\ectitle}{No \texttt{$\backslash$title} defined!}
\renewcommand{\title}[1]{\renewcommand{\ectitle}{#1}\hypersetup{pdftitle={#1}}}
\newcommand{\ecshort}{\ectitle}
\newcommand{\short}[1]{\renewcommand{\ecshort}{#1}}
% Author(s) and institutes
\newcommand{\ecauthor}{No \texttt{$\backslash$author} defined!}
\renewcommand{\author}[1]{\renewcommand{\ecauthor}{#1}\setcounter{page}{0}\hypersetup{pdfauthor={#1}}}
\newcommand{\autref}[1]{\if\thepage0\else\hyperlink{aut#1}{$^#1$}\fi}
\newcommand{\sponsor}[1]{\if\thepage0\else\footnote{#1}\fi}
\newcommand{\ecinstitute}{No \texttt{$\backslash$institute} defined!}
\newcommand{\institute}[1]{\renewcommand{\ecinstitute}{#1}}
\newcommand{\autlabel}[1]{\hypertarget{aut#1}{$^#1$}}
% Abstract and keywords
\newcommand{\ecabstract}{No \texttt{$\backslash$abstract} defined!}
\renewcommand{\abstract}[1]{\renewcommand{\ecabstract}{#1}}
\newcommand{\eckeywords}{No \texttt{$\backslash$keywords} defined!}
\newcommand{\keywords}[1]{\renewcommand{\eckeywords}{#1}\hypersetup{pdfkeywords={#1}}}
% ===================
% Headers and footers
% ===================
% Odd page header
% ---------------
\def\@oddhead{\vbox{%
  \includegraphics[width=30pt]{easst}% Logo on the left
  \hfill%
  \textsf{ECEASST}% ECEASST on the right
  \vskip 3pt%
  {\color{easstblue}\hrule height 2pt}}}
% Odd page footer
% ---------------
\def\@oddfoot{\vbox{%
  {\color{easstblue}\hrule height 2pt}
  \vskip 3pt%
  \textsf{\thepage\ / \pageref*{lastpage}}% Page number on the left
  \hfill%
  \textsf{\ecvolnumber}}}% Volume on the right
% Even page header
% ----------------
\def\@evenhead{\vbox{%
  \textsf{\ecshort}% Short title on the left
  \hfill%
  \includegraphics[width=30pt]{easst}% Logo on the right
  \vskip 3pt%
  {\color{easstblue}\hrule height 2pt}}}
% Even page footer
% ----------------
\def\@evenfoot{\vbox{%
  {\color{easstblue}\hrule height 2pt}
  \vskip 3pt%
  \textsf{\ecvolshort}% Short volume title on the left
  \hfill%
  \textsf{\thepage\ / \pageref*{lastpage}}}}% Page number on the right
% ===========================================================
% Making the title page and the frontmatter on the first page
% ===========================================================
% Define a label for the last page
\AtEndDocument{%
  \clearpage%
  \addtocounter{page}{-1}%
  \immediate\write\@auxout{\string
  \newlabel{lastpage}{{}{\thepage}{}{}}}%
  \addtocounter{page}{1}}
% Head building block for the cover page
\newcommand{\eccoverhead}{%
  % Title box
  \vspace*{-85pt}
  \noindent \colorbox{easstblue}{\parbox{414pt}{\color{white}\sf
    \vspace{6pt}
    \hspace{6pt}{\LARGE Electronic Communications of the EASST}\\[6pt]
    \hspace*{6pt}{\LARGE \ecvolnumber}
    \vspace{6pt}}}
  % EASST logo
  \begin{flushright}
    \includegraphics[height=80pt]{easst}
  \end{flushright}}
% Foot building block for the cover page
\newcommand{\eccoverfoot}{%
  % Information on editors, ECEASST home page and ISSN
  \vfill
  \colorbox{easstblue}{\parbox{414pt}{\color{white}\sf
    \vspace{6pt}
    \hspace{6pt}\eceditor\\
    %\hspace*{6pt}Managing Editors: Tiziana Margaria, Julia Padberg, Gabriele Taentzer\\
    \hspace*{6pt}ECEASST Home Page: \href{http://www.easst.org/eceasst/}{\textcolor{yellow}{http://www.easst.org/eceasst/}}
    \hfill ISSN 1863-2122\hspace{6pt}
    \vspace{6pt}}}}
% Introduce the maketitle command
\renewcommand{\maketitle}{%
  % The cover page
  % --------------
  \thispagestyle{empty}
  \enlargethispage{30pt}
  % Will be page 0, s.t. contents start on page 1
  \setcounter{page}{0}
  \eccoverhead
  % Volume and article title, author(s)
  \vspace{60pt}
  \begin{center}
    {\LARGE\ecvoltitle\par}
    \vspace{44pt}
    {\Large\ectitle\par}
    \vspace{11pt}
    \ecauthor\\[11pt]
    \pageref*{lastpage} pages
  \end{center}
  \eccoverfoot
  \newpage
  % Beginning of article title on first page
  % ----------------------------------------
  \global\@topnum\z@ % To prevent floats above the title
  \setlength{\parskip}{11pt}
  % Change footnotes to symbols
  \renewcommand{\thefootnote}{\fnsymbol{footnote}}
  % Information on title, author(s) and institutes of authors centered
  \begin{center}
    {\Large\bfseries\ectitle\par}
    {\large\bfseries\ecauthor\par}
    \ecinstitute
  \end{center}
  % Reset footnote counter and change to arabic numbers
  \setcounter{footnote}{0}
  \renewcommand{\thefootnote}{\arabic{footnote}}
  % Abstract and keywords as a block quote
  \begin{quote}
    \textbf{Abstract:} \ecabstract\par
    \textbf{Keywords:} \eckeywords
  \end{quote}
  \setlength{\parskip}{0pt}}
% Introduce the prefacetitle command
\newcommand{\prefacetitle}{%
  % The cover page
  % --------------
  \thispagestyle{empty}
  \enlargethispage{30pt}
  % Will be page 0, s.t. contents start on page 1
  \setcounter{page}{0}
  \eccoverhead
  % Volume and article title, author(s)
  \vspace{60pt}
  \begin{center}
    {\LARGE\ecvoltitle\par}
    \vspace{44pt}
    {\Large Preface\par}
    \vspace{11pt}
    \pageref*{lastpage} pages
  \end{center}
  \eccoverfoot
  \newpage
  % Beginning of article title on first page
  % ----------------------------------------
  \global\@topnum\z@ % To prevent floats above the title
  \setlength{\parskip}{11pt}
  % Preface title centered
  \begin{center}
    {\Large\bfseries Preface}
  \end{center}
  \renewcommand{\ecshort}{Preface}
  % Footnotes as arabic numbers
  \renewcommand{\thefootnote}{\arabic{footnote}}
  \setlength{\parskip}{0pt}}
