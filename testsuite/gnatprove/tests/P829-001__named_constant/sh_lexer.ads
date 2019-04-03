with Sh_Buffers; use Sh_Buffers;

package Sh_Lexer is

   type Token_Type is
     (T_NULL,
      T_WORD,         -- word token
      T_EOF,          -- end of file token
      T_ASSIGNMENT,   -- variable assignment token

      --  Operators

      T_DSEMI,        -- ';;'
      T_AND_IF,       -- '&&'
      T_AND,          -- '&'
      T_OR_IF,        -- '||'
      T_PIPE,         -- '|'

      --  Output redirection operators

      T_DGREAT,       -- '>>'
      T_CLOBBER,      -- '>|'
      T_GREATAND,     -- '>&'
      T_GREAT,        -- '>'

      --  Input redirection operators

      T_LESS,         -- '<'
      T_DLESS,        -- '<<'
      T_DLESSDASH,    -- '<<-'
      T_LESSAND,      -- '<&'
      T_LESSGREAT,    -- '<>'

      T_IO_NUMBER,

      T_NEWLINE,      -- LF
      T_LPAR,         -- '('
      T_SEMI,         -- ';'
      T_RPAR,         -- ')'

      --  Keywords

      T_IF,           -- 'if'
      T_THEN,         -- 'then'
      T_ELSE,         -- 'else'
      T_ELIF,         -- 'elif'
      T_FI,           -- 'fi'
      T_DO,           -- 'do'
      T_DONE,         --  'done'
      T_BANG,         -- '!'
      T_IN,           -- 'in'
      T_CASE,         -- 'case'
      T_ESAC,         -- 'esac'
      T_WHILE,        -- 'while'
      T_UNTIL,        -- 'until'
      T_FOR,          -- 'for'
      T_LBRACE,       -- '}'
      T_RBRACE       -- '{'
      );   -- number preceding a redirection operator
   type Token is private;
   --  T is the type of the token. If T = T_WORD then S contains the word.
   --  Lineno and Columnno are the position of the token in the file.

   Null_Token  : constant Token;


private

   type Token is record
      Kind     : Token_Type := T_WORD;
      First    : Text_Position;
      Last     : Text_Position;
   end record;

   Null_Token : constant Token := (T_WORD,
                                   Null_Text_Position,
                                   Null_Text_Position);


end Sh_Lexer;
