package body Debug_Pack is

   procedure Debug_Print (Str : String) is
      C_Str : char_array := To_C (Str);
      Res : Integer;
   begin
      Res := C_ConsolePuts (C_Str);
   end Debug_Print;

   function To_C (Item : Character) return char is
   begin
      return char'Val (Character'Pos (Item));
   end To_C;

   function To_C
     (Item       : String;
      Append_Nul : Boolean := True) return char_array
   is
   begin
      if Append_Nul then
         declare
            R : char_array (0 .. Item'Length);

         begin
            for J in Item'Range loop
               R (size_t (J - Item'First)) := To_C (Item (J));
            end loop;

            R (R'Last) := nul;
            return R;
         end;

      --  Append_Nul False

      else
         --  A nasty case, if the string is null, we must return a null
         --  char_array. The lower bound of this array is required to be zero
         --  (RM B.3(50)) but that is of course impossible given that size_t
         --  is unsigned. According to Ada 2005 AI-258, the result is to raise
         --  Constraint_Error. This is also the appropriate behavior in Ada 95,
         --  since nothing else makes sense.

         if Item'Length = 0 then
            raise Constraint_Error;

         --  Normal case

         else
            declare
               R : char_array (0 .. Item'Length - 1);

            begin
               for J in Item'Range loop
                  R (size_t (J - Item'First)) := To_C (Item (J));
               end loop;

               return R;
            end;
         end if;
      end if;
   end To_C;

end Debug_Pack;
