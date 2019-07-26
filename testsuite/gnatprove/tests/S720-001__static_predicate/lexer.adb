package body Lexer with
   SPARK_Mode
is
   C : Character;

   procedure Read_Token is
      subtype Symbol_Extra_Chars is Character
        with Static_Predicate => Symbol_Extra_Chars = '~';
   begin
      loop
         case C is
            when Symbol_Extra_Chars =>
               exit;

            when '"' =>
               pragma Assert (False);  -- @ASSERT:FAIL
               exit;

            when others =>
               pragma Assert (False);  -- @ASSERT:FAIL
               exit;
         end case;
      end loop;
   end Read_Token;

end Lexer;
