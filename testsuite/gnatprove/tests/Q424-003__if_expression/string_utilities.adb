package body String_Utilities with SPARK_Mode is

   function Longest_Common_Subsequence
     (S1, S2 : String)
      return String
   is
      subtype S1_Index is Integer range S1'Range;
      subtype S2_Index is Integer range S2'Range;

      type Seq_Length is new Integer
        range 0 .. Integer'Max (S1'Length, S2'Length);

      Lengths : array (S1_Index, S2_Index) of Seq_Length;

      function Get_Length (X1 : Integer; X2 : Natural) return Seq_Length is
        (if X1 in S1_Index and X2 in S2_Index
         then Lengths (X1, X2)
         else 0);

      function Get_Length2 (X1 : Integer; X2 : Natural) return Seq_Length is
         (case X1 is
            when 0 .. 10 =>
               (case X2 is
                  when 0 .. 10 =>
                     Lengths (X1, X2),
                  when others =>
                     0),
            when others =>
                0);

    begin
      for X1 in S1_Index loop
         for X2 in S2_Index loop
            declare
               Current_Length : Seq_Length renames Lengths (X1, X2);
            begin
               if S1 (X1) = S2 (X2) then
                  Current_Length := 1 + Get_Length (X1 - 1, X2 - 1);
               else
                  Current_Length := Seq_Length'Max (Get_Length (X1 - 1, X2),
                                                    Get_Length (X1, X2 - 1));
               end if;
            end;
         end loop;
      end loop;

      if Get_Length (S1'Last, S2'Last) = 0 then
         return "";
      end if;

      declare
         Last   : constant Integer := Integer (Get_Length (S1'Last, S2'Last));
         Result : String (1 .. Last);
         Rx     : Integer range 1 .. Result'Last := Result'Last;
         X1     : S1_Index := S1_Index'Last;
         X2     : S2_Index := S2_Index'Last;
      begin
         loop
            if S1 (X1) = S2 (X2) then
               Result (Rx) := S1 (X1);
               if Rx = Result'First then
                  return Result;
               end if;
               Rx := Rx - 1;
               X1 := X1 - 1;
               X2 := X2 - 1;
            elsif Get_Length (X1, X2 - 1) < Get_Length (X1 - 1, X2) then
               X1 := X1 - 1;
            else
               X2 := X2 - 1;
            end if;
         end loop;
      end;
  end Longest_Common_Subsequence;

end String_Utilities;
