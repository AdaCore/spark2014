package body Aida.Strings.Generic_Immutable_Unbounded_String with SPARK_Mode is

   function Length (This : T) return Ada.Containers.Count_Type is (Char_Vectors.Length (This.Text));

   function Char_At (This  : T;
                     Index : Positive) return Character is
   begin
      return Char_Vectors.Element (Container => This.Text,
                                   Index     => Index);
   end Char_At;

   function To_String (This : T) return String is
      L : Ada.Containers.Count_Type := Char_Vectors.Length (This.Text);
   begin
      if L = 0 then
         return "";
      end if;

      if L < MAX_LENGTH then
         declare
            R : String (1..Positive (Char_Vectors.Length (This.Text))) := (others => ' ');
         begin
            for I in Positive range 1..Positive (Char_Vectors.Length (This.Text)) loop
               R (I) := Char_Vectors.Element (Container => This.Text,
                                              Index  => I);
            end loop;
            return R;
         end;
      else
         raise Out_Of_Bounds_Exception;
      end if;
   end To_String;

end Aida.Strings.Generic_Immutable_Unbounded_String;
