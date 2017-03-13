package body Tab is
   procedure Tab_Filter (B : in Arr; Threshold : in Integer; A : in out Arr)
   is
      Cur : Index'Base := Index'First - 1;

      function Prev (X : Index) return Index'Base is (X - 1);
   begin
      for I in Index'First .. Index'Last loop
         pragma Loop_Invariant (Cur in Cur'Loop_Entry .. Prev (I));
         pragma Loop_Invariant
           (for all J in Index range Index'First .. Prev(I) =>
              (if (B(J) > Threshold) then
                 (for some K in Index range 1 .. Cur => (A(K)=B(J)))));
         if (B(I) > Threshold) then
            Cur := Cur + 1;
            A (Cur) := B(I);
         end if;
      end loop;
   end Tab_Filter;
end Tab;
