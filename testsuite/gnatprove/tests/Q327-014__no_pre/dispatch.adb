package body Dispatch with SPARK_Mode is

   function Incr (X : Root) return Root is
   begin
      return (F => X.F + 1);
   end Incr;

   function Incr2 (X : Root) return Root is
   begin
      return (F => X.F + 1); --@OVERFLOW_CHECK:FAIL
   end Incr2;

   function Incr3 (X : Root) return Root is
   begin
      if X.F < Integer'Last then
         return (F => X.F + 1);
      else
         return (F => 0);
      end if;
   end Incr3;

   function Incr4 (X : Root) return Root is
   begin
      return (F => X.F + 1);
   end Incr4;

   function Incr5 (X : Root) return Root is
   begin
      return (F => X.F + 1);
   end Incr5;

   function Incr6 (X : Root) return Root is
   begin
      if X.F < Integer'Last then
         return (F => X.F + 1);
      else
         return (F => 0);
      end if;
   end Incr6;

end Dispatch;
