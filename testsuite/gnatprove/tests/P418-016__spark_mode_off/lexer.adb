with Names; use Names;

procedure Lexer is
   type Token_Kind is (T_Symbol,
                       T_EOF);

   type Token (Kind : Token_Kind := T_EOF) is record
      case Kind is
         when T_Symbol =>
            Name : Name_Id;
         when others =>
            null;
      end case;
   end record;

   T : Token;
begin
   T := (Kind => T_EOF);
end Lexer;
