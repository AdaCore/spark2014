with Ada.Containers; use Ada.Containers;
with Seq; use Seq;
with Lists; use Lists;
procedure Linear_Search
   with SPARK_Mode
is
    subtype Index_Or_Zero is Natural range 0 .. 10;
    subtype Index is Index_Or_Zero range 1 .. 10;
    type Int_Array is array (Index) of Integer;

    function Search (Arr : Int_Array; N : Integer) return Index_Or_Zero
      with Post => (if Search'Result = 0 then
                      (for all E of Arr => E /= N)
                    else
                      (Arr (Search'Result) = N))
    is
       I      : Index := 1;
    begin
       while I < 10 loop
          pragma Loop_Invariant (for all J in Index'First .. I-1 =>
                                   (Arr (J) /= N));
          if Arr (I) = N then
             return I;
          end if;
          I := I + 1;
       end loop;

       return 0;
    end Search;

   subtype Int_Seq is Seq.Sequence;

   function Search (Arr : Int_Seq; N : Integer) return Index_Or_Zero with
     Pre => Last (Arr) = 10,
     Post => (if Search'Result = 0 then
                (for all E of Arr => E /= N)
                  else
                (Get (Arr, Search'Result) = N))
   is
       I      : Index := 1;
    begin
       while I < 10 loop
          pragma Loop_Invariant (for all J in Index'First .. I-1 =>
                                   (Get (Arr, J) /= N));
          if Get (Arr, I) = N then
             return I;
          end if;
          I := I + 1;
       end loop;

       return 0;
    end Search;

   subtype Int_List is Lists.List;

   function Search (Arr : Int_List; N : Integer) return Cursor with
     Pre => Formal_Model.M.Last (Formal_Model.Model (Arr)) = 10,
     Post => (if Search'Result = No_Element then
                (for all E of Arr => E /= N)
                  else
                (Element (Arr, Search'Result) = N))
   is
      I : Count_Type := 1;
      C : Cursor := First (Arr);
   begin
      while I < 10 loop
         pragma Loop_Invariant (Has_Element (Arr, C));
         pragma Loop_Invariant (Formal_Model.P.Get (Formal_Model.Positions (Arr), C) = I);
         pragma Loop_Invariant (for all J in 1 .. I-1 =>
                                  (Formal_Model.M.Get (Formal_Model.Model (Arr), J) /= N));
         if Element (Arr, C) = N then
            return C;
         end if;
         I := I + 1;
         Next (Arr, C);
      end loop;

      return No_Element;
   end Search;
begin
    null;
end Linear_Search;
