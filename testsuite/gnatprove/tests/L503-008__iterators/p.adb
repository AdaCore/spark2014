package body P is 

   procedure Iter_Over_Array (A : Ar) is
      Sum : Integer := 0;
   begin
      for X of A loop
         Sum := Sum + X;
      end loop;
   end Iter_Over_Array;

    procedure Quant_Over_Array(A : in out Ar) is
    begin
       for I in A'Range loop
          pragma Assert (for all J in A'First .. I - 1 => A (J) = 0);
          A (I) := 0;
       end loop;
    end Quant_Over_Array;

    procedure Iter_Over_Lists (X : My_Lists.List) is
       Sum : Integer := 0;
       C   : My_Lists.Cursor;
    begin
       C := X.First;
       while C /= My_Lists.No_Element loop
          Sum := Sum + My_Lists.Element(X, C);
          My_Lists.Next (X, C);
       end loop;
    end Iter_Over_Lists;

    procedure Quant_Over_Lists (X : My_Lists.List) is
    begin
       null;
    end Quant_Over_Lists;

end P;
