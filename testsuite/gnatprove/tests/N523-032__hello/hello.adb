with Ada.Characters.Handling; use Ada.Characters.Handling;
with Ada.Text_IO;

package body Hello
   with Spark_Mode => On
is

   G_Lang_Level : Language_Level;

   function To_Caml_Char
     (Str : String; Res : String; J : Integer) return Boolean
   is
     (if J = Str'First then
        Res (J) = To_Upper (Str (J))
      elsif Str (J - 1) not in 'a' .. 'z'
        and then Str (J - 1) not in 'A' .. 'Z'
      then
         Res (J) = To_Upper (Str (J))
      else
         Res (J) = To_Lower (Str (J)))
   with Pre =>
      J in Str'Range and J in Res'Range;

   function To_Caml_Char2
     (Str : String; Res : String; Last : Integer) return Boolean
   is
     (for all J in Str'First .. Last =>
        (if J = Str'First then
              Res (J) = To_Upper (Str (J))
         elsif Str (J - 1) not in 'a' .. 'z'
         and then Str (J - 1) not in 'A' .. 'Z'
         then
            Res (J) = To_Upper (Str (J))
         else
            Res (J) = To_Lower (Str (J))))
   with Pre =>
      Last <= Str'Last and Str'Last = Res'Last and Str'First = Res'First;

   function To_Camel_Case (Str : String) return String
     with Post =>
       To_Camel_Case'Result'First = Str'First
     and then
       To_Camel_Case'Result'Last = Str'Last
     and then
       To_Caml_Char2 (Str, To_Camel_Case'Result, Str'Last);

   -------------------
   -- To_Camel_Case --
   -------------------

   function To_Camel_Case (Str : String) return String
   is
      Ret   : String(Str'First .. Str'Last) := Str;
      To_Up : Boolean := True;

   begin
      for Idx in Str'Range loop
         if To_Up then
            Ret (Idx) := To_Upper (Ret (Idx));
         else
            Ret (Idx) := To_Lower (Ret (Idx));
         end if;

         pragma Assert (Str'First = Ret'First and then Str'Last = Ret'Last);
         pragma Assert (Idx in Str'Range);
         pragma Assert (Idx in Ret'Range);
         pragma Loop_Invariant (To_Caml_Char2 (Str, Ret, Idx));
         pragma Loop_Invariant
           (for all J in Idx .. Str'Last =>
              (if J > Idx then Ret (J) = Str (J)));

         if Str (Idx) not in 'A'..'Z'
           and then Str (Idx) not in 'a'..'z'
         then
            --  Not a letter: next character will be upper case
            To_Up := True;
         else
            To_Up := False;
         end if;
      end loop;
      pragma Assert (Str'First = Ret'First and then Str'Last = Ret'Last);

      return Ret;
   end To_Camel_Case;

   ------------------------
   -- Set_Language_Level --
   ------------------------

   procedure Set_Language_Level (Level : Language_Level)
   is
   begin
      G_Lang_Level := Level;
   end Set_Language_Level;

   ---------------
   -- Say_Hello --
   ---------------

   procedure Say_Hello
     (Who   : in String)
   is
      Hello  : constant String :=
                 (case G_Lang_Level is
                  when Formal => "Hello",
                  when Casual => "Hi");
      Prefix : constant String :=
                 (if Who'Length = 0
                  then ""
                  else " ");

   begin
      Ada.Text_IO.Put_Line (Hello & Prefix & To_Camel_Case (Who) & "!");
   end Say_Hello;

end Hello;

