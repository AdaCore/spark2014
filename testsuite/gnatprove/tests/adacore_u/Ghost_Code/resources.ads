package Resources
  with SPARK_Mode
is
   subtype Resource is Natural range 0 .. 1000;
   subtype Num is Natural range 0 .. 6;
   subtype Index is Num range 1 .. 6;
   type Data is array (Index) of Resource;

   function Sum (D : Data; To : Num) return Natural is
      (if To = 0 then 0 else D(To) + Sum(D,To-1))
   with Ghost, Annotate => (GNATprove, Terminating);
--   pragma Annotate (GNATprove, Terminating, Sum);

   procedure Create (D : out Data) with
     Post => Sum (D, D'Last) < 42;

   procedure Remove (D : in out Data; J : Index) with
     Pre  => Sum (D, D'Last) < 42,
     Post => Sum (D, D'Last) < 42;

end Resources;
