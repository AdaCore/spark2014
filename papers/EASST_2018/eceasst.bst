% EC-EASST bibliography style
% Bibliography style for use in articles for the
% "Electronic Communications of the EASST"

% Fields
% ======
% Additional fields "doi" and "url" for information
% on online availability

ENTRY
  { address
    author
    booktitle
    chapter
    doi
    edition
    editor
    howpublished
    institution
    journal
    key
    month
    note
    number
    organization
    pages
    publisher
    school
    series
    title
    type
    url
    volume
    year }
  {}
  { label extra.label sort.label }

% Macros for month names
% ======================

MACRO {jan} {"Jan."}
MACRO {feb} {"Feb."}
MACRO {mar} {"Mar."}
MACRO {apr} {"Apr."}
MACRO {may} {"May"}
MACRO {jun} {"June"}
MACRO {jul} {"July"}
MACRO {aug} {"Aug."}
MACRO {sep} {"Sept."}
MACRO {oct} {"Oct."}
MACRO {nov} {"Nov."}
MACRO {dec} {"Dec."}

% Formatting Helper Functions
% ===========================

% Add a comma between top two stack elements if both are non-empty
FUNCTION {format.insert.comma}
{ duplicate$ empty$
    'pop$                           % second empty, first left
    { swap$ duplicate$ empty$
        'pop$                       % second empty, first left
        { ", " * swap$ * }          % first ", " second left
      if$ }
  if$ }

% Short editors without punctuation (for "In" clauses)
FUNCTION {format.editors.short}
{ editor empty$
    { "" }
    { editor #1 "{ll}" format.name$
      editor num.names$ duplicate$
      #2 >
        { pop$ " et~al. (eds.)" * }
        { #2 <
            { " (ed.)" * }
            { editor #2 "{ff }{vv }{ll}{ jj}" format.name$ "others" =
                { " et~al. (eds.)" * }
                { " and " *
                  editor #2 "{ll}" format.name$ *
                  " (eds.)" * }
              if$ }
          if$ }
      if$ }
  if$ }

% Book title without punctuation (for "In" clauses)
FUNCTION {format.booktitle}
{ booktitle empty$
    { "" }
    { "\emph{" booktitle * "}" * }
  if$ }

% Date without punctuation (to be used after
% publisher or journal, includes month and year)
FUNCTION {format.date}
{ year empty$
    { month empty$
        { "" }
        { "there's a month but no year in " cite$ * warning$
          month }
      if$ }
    { month empty$
        'year
        { month " " * year * }
      if$ }
  if$ }

% Volume and number (if only one is given, printed
% plain, if both are given, vol(num))
FUNCTION {format.vol.num}
{ volume empty$
    { number empty$
        { "" }
        { number }
      if$ }
    { number empty$
        { volume }
        { volume "(" * number * ")" * }
      if$ }
  if$ }

% Pages dashified
STRINGS { rest }
FUNCTION {format.pages}
{ pages empty$
    { "" }
    { pages 'rest :=
      ""
        { rest empty$
            { #0 }
            { #1 }
          if$ }
        { rest #1 #1 substring$ "-" =
            { "--" *
                { rest #1 #1 substring$ "-" = }
                { rest #2 global.max$ substring$ 'rest := }
              while$ }
            { rest #1 #1 substring$ *
              rest #2 global.max$ substring$ 'rest := }
          if$ }
      while$ }
  if$ }

% Are there multiple pages?
INTEGERS { multi }
FUNCTION {multiple.pages}
{ pages 'rest :=
  #0 'multi :=
    { multi
        { #0 }
        { rest empty$
            { #0 }
            { #1 }
          if$ }
      if$ }
    { rest #1 #1 substring$
      duplicate$ "-" =
        { #1 'multi := }
        'skip$
      if$
      duplicate$ "," =
        { #1 'multi := }
        'skip$
      if$
      "+" =
        { #1 'multi := }
        'skip$
      if$
      rest #2 global.max$ substring$ 'rest := }
  while$
  multi }

FUNCTION {format.series.vol.num}
{ series empty$
    { "" }
    { series }
  if$
  format.vol.num
  duplicate$ empty$
    'pop$
    { swap$ duplicate$ empty$
        { pop$
          "Volume~" swap$ * }
        { "~" * swap$ * }
      if$ }
  if$ }

FUNCTION {format.add.chapter}
{ chapter empty$
    'skip$
    { chapter
      swap$ duplicate$ empty$
        { pop$                  % Previous empty, chapter left on stack
          type empty$
            { "Chapter~" swap$ * }
            { type "t" change.case$
              "~" * swap$ * }
          if$ }
        { type empty$
            { ", chapter~" * swap$ * }
            { ", " *
              type "l" change.case$ *
              "~" * swap$ * }
          if$ }
      if$ }
  if$ }

FUNCTION {format.add.pages}
{ format.pages                  % Previous information and pages on stack
  duplicate$ empty$
    'pop$
    { swap$ duplicate$ empty$
        { pop$                  % Previous empty, pages left on stack
          multiple.pages
            { "Pp.~" swap$ * }
            { "P.~" swap$ * }
          if$ }
        { multiple.pages        % Previous ", " pages left on stack
            { ", pp.~" * swap$ * }
            { ", p.~" * swap$ * }
          if$ }
      if$ }
  if$ }

% Field Output Functions
% ======================

% Helper function for writing non-empty stack content
FUNCTION {output.nonnull}
{ add.period$
  write$
  newline$ }

% Helper function to test for non-emptiness and write
FUNCTION {output}
{ duplicate$ empty$
    'pop$
    'output.nonnull
  if$ }

% Helper function for formatting author and editor names
STRINGS { names name }
INTEGERS { ptr left }
FUNCTION {format.names}
{ 'names :=
  #1 'ptr :=
  names num.names$ 'left :=
    { left #0 > }
    { names ptr "{f.~}{vv~}{ll}{, jj}" format.name$ 'name :=
      ptr #1 >
        { left #1 >
            { ", " * name * }
            { name "others" =
                { " et~al." * }
                { ", " * name * }
              if$ }
          if$ }
        'name
      if$
      ptr #1 + 'ptr :=
      left #1 - 'left := }
  while$ }

% Authors of a contribution with period and newline
% Field: author
FUNCTION {output.authors}
{ author empty$
    'skip$
    { author format.names
      output.nonnull }
  if$ }

% Editors of a book or proceedings with period and newline
% Field: editor
FUNCTION {output.editors}
{ editor empty$
    'skip$
    { editor format.names
      editor num.names$ #1 >
        { " (eds.)" * }
        { " (ed.)" * }
      if$
      output.nonnull }
  if$ }

% Minor title (article, master's thesis, ...)
% with period and newline
% Field: title
FUNCTION {output.minortitle}
{ title output }

% Major title (book, PhD thesis, ...)
% with period and newline
% Field: title
FUNCTION {output.majortitle}
{ title empty$
    'skip$
    { "\emph{" title * "}" *
      output.nonnull }
  if$ }

% Journal information
% This fairly complex function does its best to put the pieces of journal
% information together in a readable way.
% Fields: journal, volume, number, pages, month, year
FUNCTION {output.journal}
{ journal empty$
    { "" }
    { "\emph{" journal * "}" * }
  if$
  format.vol.num
  format.pages
  duplicate$ empty$
    { pop$                          % pages empty, journal and volnum on stack
      duplicate$ empty$
        'pop$                       % volnum empty, journal left on stack
        { swap$ duplicate$ empty$
            'pop$                   % journal empty, volnum left on stack
            { " " * swap$ * }       % journal " " volnum left on stack
          if$ }
      if$ }
    { swap$ duplicate$ empty$
        { pop$ pop$                 % volnum empty, leave journal on stack
          format.add.pages }        % and use format.add.pages
        { ":" * swap$ *             % journal and volnum ":" pages on stack
          swap$ duplicate$ empty$
            'pop$                   % journal empty, volnum ":" pages left
            { " " * swap$ * }       % journal " " volnum ":" pages left on stack
          if$ }
      if$ }
  if$
  format.date
  format.insert.comma
  output }

FUNCTION {output.journal.crossref}
{ "In \cite{" crossref * "}" *
  format.add.pages
  output.nonnull }

% Fields: series, volume, number
FUNCTION {output.series}
{ format.series.vol.num
  output }

FUNCTION {output.series.crossref}
{ format.vol.num
  duplicate$ empty$
    { pop$
      "In \cite{" crossref * "}" * }
    { "Volume " swap$ *
      " in \cite{" * crossref * "}" * }
  if$
  edition empty$
    'skip$
    { ", " *
      edition "l" change.case$ *
      " edition" * }
  if$
  format.date
  format.insert.comma
  output.nonnull }

% Fields: series, volume, number, type, chapter, pages
FUNCTION {output.series.pages}
{ format.series.vol.num
  format.add.chapter
  format.add.pages
  output }

FUNCTION {output.series.pages.crossref}
{ format.vol.num
  duplicate$ empty$
    { pop$
      "In \cite{" crossref * "}" * }
    { "Volume " swap$ *
      " in \cite{" * crossref * "}" * }
  if$
  format.add.chapter
  format.add.pages
  edition empty$
    'skip$
    { ", " *
      edition "l" change.case$ *
      " edition" * }
  if$
  format.date
  format.insert.comma
  output.nonnull }

FUNCTION {output.book.crossref}
{ ""
  format.add.chapter
  format.add.pages
  duplicate$ empty$
    { "In " * }
    { " in " * }
  if$
  "\cite{" * crossref * "}" *
  output.nonnull }

% Fields: editor, booktitle
FUNCTION {output.booktitle}
{ format.editors.short
  format.booktitle
  format.insert.comma
  duplicate$ empty$
    'pop$
    { "In " swap$ *
      output.nonnull }
  if$ }

% Fields: publisher, address, edition, month, year
FUNCTION {output.publisher}
{ publisher
  address
  format.insert.comma
  edition empty$
    'skip$
    { duplicate$ empty$
        { edition "t" change.case$ *
          " edition" * }
        { ", " *
          edition "l" change.case$ *
          " edition" * }
      if$ }
  if$
  format.date
  format.insert.comma
  output }

% Fields: type, school, address, month, year
FUNCTION {output.school}
{ type empty$
    'skip$
    { pop$
      type "t" change.case$ }
  if$
  school
  format.insert.comma
  address
  format.insert.comma
  format.date
  format.insert.comma
  output }

% Fields: howpublished, address, month, year
FUNCTION {output.howpublished}
{ howpublished
  address
  format.insert.comma
  format.date
  format.insert.comma
  output }

% Fields: organization, address, edition, month, year
FUNCTION {output.organization}
{ author empty$
    { "" }
    { organization }
  if$
  address
  format.insert.comma
  edition empty$
    'skip$
    { duplicate$ empty$
        { edition "t" change.case$ *
          " edition" * }
        { ", " *
          edition "l" change.case$ *
          " edition" * }
      if$ }
  if$
  format.date
  format.insert.comma
  output }

% Fields: type, number, institution, address, month, year
FUNCTION {output.techreport}
{ type empty$
    { "Technical report" }
    { type "t" change.case$ }
  if$
  number empty$
    'skip$
    { "~" * number * }
  if$
  institution
  format.insert.comma
  address
  format.insert.comma
  format.date
  format.insert.comma
  output.nonnull }

% Note, DOI and URL
% Fields: note, doi, url
FUNCTION {output.note.doi.url}
{ note empty$
    'skip$
    { note
      add.period$
      write$
      newline$ }
  if$
  doi empty$
    'skip$
    { "\\\doi{" doi * "}" *
      write$
      newline$ }
  if$
  url empty$
    'skip$
    { "\\\url{" url * "}" *
      write$
      newline$ }
  if$ }

% Entry Type Functions
% ====================

% Helper function for writing the bibitem
% used in all entry types
FUNCTION {output.bibitem}
{ newline$
  "\bibitem[" write$
  label write$
  "]{" write$
  cite$ write$
  "}" write$
  newline$ }

% Required: author, title, journal, year
% Optional: volume, number, pages, month,
%           note, doi(!), url(!)
FUNCTION {article}
{ output.bibitem
  author empty$
    { "empty author in article " cite$ * warning$ }
    'output.authors
  if$
  title empty$
    { "empty title in article " cite$ * warning$ }
    'output.minortitle
  if$
  crossref missing$
    { journal empty$
        { "empty journal in article " cite$ * warning$ }
        'skip$
      if$
      year empty$
        { "empty year in article " cite$ * warning$ }
        'skip$
      if$
      output.journal }
    'output.journal.crossref
  if$
  output.note.doi.url }

% Required: author or editor, title, publisher, year
% Optional: series, volume(!), number(!), address, edition, month,
%           note, doi(!), url(!)
FUNCTION {book}
{ output.bibitem
  author empty$
    { editor empty$
        { "empty author and editor in book " cite$ * warning$ }
        'output.editors
      if$ }
    'output.authors
  if$
  title empty$
    { "empty title in book " cite$ * warning$ }
    'output.majortitle
  if$
  crossref missing$
    { output.series
      publisher empty$
        { "empty publisher in book " cite$ * warning$ }
        'skip$
      if$
      year empty$
        { "empty year in book " cite$ * warning$ }
        'skip$
      if$
      output.publisher }
    'output.series.crossref
  if$
  output.note.doi.url }

% Required: title
% Optional: author, howpublished, address, month, year,
%           note, doi(!), url(!)
FUNCTION {booklet}
{ output.bibitem
  output.authors
  title empty$
    { "empty title in booklet " cite$ * warning$ }
    'output.minortitle
  if$
  output.howpublished
  output.note.doi.url }

% Required: author or editor, title, chapter and/or pages, publisher, year
% Optional: series, volume(!), number(!), type, address, edition, month,
%           note, doi(!), url(!)
FUNCTION {inbook}
{ output.bibitem
  author empty$
    { editor empty$
        { "empty author and editor in inbook " cite$ * warning$ }
        'output.editors
      if$ }
    'output.authors
  if$
  title empty$
    { "empty title in inbook " cite$ * warning$ }
    'output.majortitle
  if$
  pages empty$
    { chapter empty$
        { "empty chapter and pages in inbook " cite$ * warning$ }
        'skip$
      if$ }
    'skip$
  if$
  crossref empty$
    { output.series.pages
      publisher empty$
        { "empty publisher in inbook " cite$ * warning$ }
        'skip$
      if$
      year empty$
        { "empty year in inbook " cite$ * warning$ }
        'skip$
      if$
      output.publisher }
    'output.series.pages.crossref
  if$
  output.note.doi.url }

% Required: author, title, booktitle, publisher, year
% Optional: editor, series, volume(!), number(!), type, chapter, pages,
%           address, edition, month,
%           note, doi(!), url(!)
FUNCTION {incollection}
{ output.bibitem
  author empty$
    { "empty author in incollection " cite$ * warning$ }
    'output.authors
  if$
  title empty$
    { "empty title in incollection " cite$ * warning$ }
    'output.minortitle
  if$
  crossref missing$
    { booktitle empty$
        { "empty booktitle in incollection " cite$ * warning$ }
        'skip$
      if$
      output.booktitle
      output.series.pages
      publisher empty$
        { "empty publisher in incollection " cite$ * warning$ }
        'skip$
      if$
      year empty$
        { "empty year in incollection " cite$ * warning$ }
        'skip$
      if$
      output.publisher }
    'output.book.crossref
  if$
  output.note.doi.url }

% Required: author, title, booktitle, year
% Optional: editor, series, volume(!), number(!), type(!), chapter(!),
%           pages, (organization), publisher, address, edition(!), month,
%           note, doi(!), url(!)
FUNCTION {inproceedings}
{ output.bibitem
  author empty$
    { "empty author in inproceedings " cite$ * warning$ }
    'output.authors
  if$
  title empty$
    { "empty title in inproceedings " cite$ * warning$ }
    'output.minortitle
  if$
  crossref missing$
    { booktitle empty$
        { "empty booktitle in inproceedings " cite$ * warning$ }
        'skip$
      if$
      output.booktitle
      output.series.pages
      year empty$
        { "empty year in inproceedings " cite$ * warning$ }
        'skip$
      if$
      output.publisher }
    'output.book.crossref
  if$
  output.note.doi.url }

% Required: title
% Optional: author, organization, address, edition, month, year,
%           note, doi(!), url(!)
FUNCTION {manual}
{ output.bibitem
  author empty$
    { organization output }
    'output.authors
  if$
  title empty$
    { "empty title in manual " cite$ * warning$ }
    'output.minortitle
  if$
  output.organization
  output.note.doi.url }

% Required: author, title, school, year
% Optional: type, address, month,
%           note, doi(!), url(!)
FUNCTION {mastersthesis}
{ output.bibitem
  author empty$
    { "empty author in mastersthesis " cite$ * warning$ }
    'output.authors
  if$
  title empty$
    { "empty title in mastersthesis " cite$ * warning$ }
    'output.minortitle
  if$
  school empty$
    { "empty school in mastersthesis " cite$ * warning$ }
    'skip$
  if$
  year empty$
    { "empty year in mastersthesis " cite$ * warning$ }
    'skip$
  if$
  "Master's thesis" output.school
  output.note.doi.url }

% Optional: author, title, howpublished, address(!), month, year,
%           note, doi(!), url(!)
FUNCTION {misc}
{ output.bibitem
  output.authors
  output.minortitle
  output.howpublished
  output.note.doi.url }

% Required: author, title, school, year
% Optional: type, address, month,
%           note, doi(!), url(!)
FUNCTION {phdthesis}
{ output.bibitem
  author empty$
    { "empty author in phdthesis " cite$ * warning$ }
    'output.authors
  if$
  title empty$
    { "empty title in phdthesis " cite$ * warning$ }
    'output.majortitle
  if$
  school empty$
    { "empty school in phdthesis " cite$ * warning$ }
    'skip$
  if$
  year empty$
    { "empty year in phdthesis " cite$ * warning$ }
    'skip$
  if$
  "PhD thesis" output.school
  output.note.doi.url }

% Required: title, year
% Optional: edtor, series, volume(!), number(!), (organization),
%           publisher, address, edition(!), month,
%           note, doi(!), url(!)
FUNCTION {proceedings}
{ output.bibitem
  output.editors
  title empty$
    { "empty title in proceedings " cite$ * warning$ }
    'output.majortitle
  if$
  output.series
  year empty$
    { "empty year in book " cite$ * warning$ }
    'skip$
  if$
  output.publisher
  output.note.doi.url }

FUNCTION {conference}
{ proceedings }

% Required: author, title, institution, year
% Optional: type, number, address, month,
%           note, doi(!), url(!)
FUNCTION {techreport}
{ output.bibitem
  author empty$
    { "empty author in techreport " cite$ * warning$ }
    'output.authors
  if$
  title empty$
    { "empty title in techreport " cite$ * warning$ }
    'output.minortitle
  if$
  institution empty$
    { "empty institution in techreport " cite$ * warning$ }
    'skip$
  if$
  year empty$
    { "empty year in techreport " cite$ * warning$ }
    'skip$
  if$
  output.techreport
  output.note.doi.url }

% Required: author, title, note
% Optional: howpublished(!), address(!), month, year,
%           doi(!), url(!)
FUNCTION {unpublished}
{ output.bibitem
  author empty$
    { "empty author in unpublished " cite$ * warning$ }
    'output.authors
  if$
  title empty$
    { "empty title in unpublished " cite$ * warning$ }
    'output.minortitle
  if$
  output.howpublished
  note empty$
    { "empty note in unpublished " cite$ * warning$ }
    'skip$
  if$
  output.note.doi.url }

FUNCTION {default.type}
{ misc }

% Alpha Label Calculation
% =======================
% Shamelessly stolen from the 'alpha' standard BibTeX style

FUNCTION {and}
{   'skip$
    { pop$ #0 }
  if$ }

FUNCTION {or}
{   { pop$ #1 }
    'skip$
  if$ }

FUNCTION {field.or.null}
{ duplicate$ empty$
    { pop$ "" }
    'skip$
  if$ }

READ

FUNCTION {sortify}
{ purify$
  "l" change.case$ }

INTEGERS { len }

FUNCTION {chop.word}
{ 'name :=
  'len :=
  name #1 len substring$ =
    { name len #1 + global.max$ substring$ }
    'name
  if$ }

INTEGERS { et.al.char.used }

FUNCTION {initialize.et.al.char.used}
{ #0 'et.al.char.used := }

EXECUTE {initialize.et.al.char.used}

INTEGERS { num }

FUNCTION {format.lab.names}
{ 'names :=
  names num.names$ 'num :=
  num #1 >
    { num #4 >
        { #3 'left := }
        { num 'left := }
      if$
      #1 'ptr :=
      ""
        { left #0 > }
        { ptr num =
            { names ptr "{ff }{vv }{ll}{ jj}" format.name$ "others" =
                { "{\etalchar{+}}" *
                  #1 'et.al.char.used := }
                { names ptr "{ll}" format.name$ #1 text.prefix$ * }
              if$ }
            { names ptr "{ll}" format.name$ #1 text.prefix$ * }
          if$
          ptr #1 + 'ptr :=
          left #1 - 'left := }
      while$
      num #4 >
        { "{\etalchar{+}}" *
          #1 'et.al.char.used := }
        'skip$
      if$
      duplicate$ }
    { names #1 "{v{}}{l{}}" format.name$
      duplicate$ text.length$ #2 <
        { pop$
          names #1 "{ll}" format.name$ #3 text.prefix$
          duplicate$ }
        { names #1 "{ll}" format.name$ #3 text.prefix$
          swap$ }
      if$ }
  if$ }

FUNCTION {author.key.label}
{ author empty$
    { key empty$
        { cite$ #1 #3 substring$
          duplicate$ }
        { key #3 text.prefix$
          duplicate$ }
      if$ }
    { author format.lab.names }
  if$ }

FUNCTION {author.editor.key.label}
{ author empty$
    { editor empty$
        { key empty$
            { cite$ #1 #3 substring$
              duplicate$ }
            { key #3 text.prefix$
              duplicate$ }
          if$ }
        { editor format.lab.names }
      if$ }
    { author format.lab.names }
  if$ }

FUNCTION {author.key.organization.label}
{ author empty$
    { key empty$
        { organization empty$
            { cite$ #1 #3 substring$
              duplicate$ }
            { "The " #4 organization chop.word #3 text.prefix$
              duplicate$ }
          if$ }
        { key #3 text.prefix$
          duplicate$ }
      if$ }
    { author format.lab.names }
  if$ }

FUNCTION {editor.key.organization.label}
{ editor empty$
    { key empty$
        { organization empty$
            { cite$ #1 #3 substring$
              duplicate$ }
            { "The " #4 organization chop.word #3 text.prefix$
              duplicate$ }
          if$ }
        { key #3 text.prefix$
          duplicate$ }
      if$ }
    { editor format.lab.names }
  if$ }

FUNCTION {calc.label}
{ type$ "book" =
  type$ "inbook" =
  or
    'author.editor.key.label
    { type$ "proceedings" =
        'editor.key.organization.label
        { type$ "manual" =
            'author.key.organization.label
            'author.key.label
          if$ }
      if$ }
  if$
  year field.or.null purify$ #-1 #2 substring$ *
  'label :=
  year field.or.null purify$ #-1 #4 substring$ *
  sortify 'sort.label := }

FUNCTION {sort.format.names}
{ 'names :=
  #1 'ptr :=
  ""
  names num.names$ 'num :=
  num 'left :=
    { left #0 > }
    { ptr #1 >
        { "   " * }
        'skip$
      if$
      names ptr "{vv{ } }{ll{ }}{  ff{ }}{  jj{ }}" format.name$ 'name :=
      ptr num = name "others" = and
        { "et al" * }
        { name sortify * }
      if$
      ptr #1 + 'ptr :=
      left #1 - 'left := }
  while$ }

FUNCTION {sort.format.title}
{ 'name :=
  "A " #2
    "An " #3
      "The " #4 name chop.word
    chop.word
  chop.word
  sortify
  #1 global.max$ substring$ }

FUNCTION {author.sort}
{ author empty$
    { key empty$
        { "to sort, need author or key in " cite$ * warning$
          "" }
        { key sortify }
      if$ }
    { author sort.format.names }
  if$ }

FUNCTION {author.editor.sort}
{ author empty$
    { editor empty$
        { key empty$
            { "to sort, need author, editor, or key in " cite$ * warning$
              "" }
            { key sortify }
          if$ }
        { editor sort.format.names }
      if$ }
    { author sort.format.names }
  if$ }

FUNCTION {author.organization.sort}
{ author empty$
    { organization empty$
        { key empty$
            { "to sort, need author, organization, or key in " cite$ * warning$
              "" }
            { key sortify }
          if$ }
        { "The " #4 organization chop.word sortify }
      if$ }
    { author sort.format.names }
  if$ }

FUNCTION {editor.organization.sort}
{ editor empty$
    { organization empty$
        { key empty$
            { "to sort, need editor, organization, or key in " cite$ * warning$
              "" }
            { key sortify }
          if$ }
        { "The " #4 organization chop.word sortify }
      if$ }
    { editor sort.format.names }
  if$ }

FUNCTION {presort}
{ calc.label
  sort.label
  "    " *
  type$ "book" =
  type$ "inbook" =
  or
    'author.editor.sort
    { type$ "proceedings" =
        'editor.organization.sort
        { type$ "manual" =
            'author.organization.sort
            'author.sort
          if$ }
      if$ }
  if$ *
  "    " *
  year field.or.null sortify *
  "    " *
  title field.or.null
  sort.format.title *
  #1 entry.max$ substring$
  'sort.key$ := }

ITERATE {presort}

SORT

STRINGS { longest.label last.sort.label next.extra }

INTEGERS { longest.label.width last.extra.num }

FUNCTION {initialize.longest.label}
{ "" 'longest.label :=
  #0 int.to.chr$ 'last.sort.label :=
  "" 'next.extra :=
  #0 'longest.label.width :=
  #0 'last.extra.num := }

FUNCTION {forward.pass}
{ last.sort.label sort.label =
    { last.extra.num #1 + 'last.extra.num :=
      last.extra.num int.to.chr$ 'extra.label := }
    { "a" chr.to.int$ 'last.extra.num :=
      "" 'extra.label :=
      sort.label 'last.sort.label := }
  if$ }

FUNCTION {reverse.pass}
{ next.extra "b" =
    { "a" 'extra.label := }
    'skip$
  if$
  label extra.label * 'label :=
  label width$ longest.label.width >
    { label 'longest.label :=
      label width$ 'longest.label.width := }
    'skip$
  if$
  extra.label 'next.extra := }

EXECUTE {initialize.longest.label}

ITERATE {forward.pass}

REVERSE {reverse.pass}

FUNCTION {begin.bib}
{ et.al.char.used
    { "\newcommand{\etalchar}[1]{$^{#1}$}" write$ newline$ }
    'skip$
  if$
  preamble$ empty$
    'skip$
    { preamble$ write$ newline$ }
  if$
  "\begin{thebibliography}{"  longest.label  * "}" * write$ newline$ }

EXECUTE {begin.bib}

ITERATE {call.type$}

FUNCTION {end.bib}
{ newline$
  "\end{thebibliography}" write$ newline$ }

EXECUTE {end.bib}
