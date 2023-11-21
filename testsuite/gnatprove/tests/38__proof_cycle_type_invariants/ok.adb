package body Ok with SPARK_Mode is

   function Init return T with Pre => True;

   function Init return T is
   begin
      return (A => True);
   end Init;

   function F (X : T) return Boolean is
      Y : T := Init;
   begin
      return True;
   end F;
end;
