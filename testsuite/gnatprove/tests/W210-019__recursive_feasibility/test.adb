procedure Test with SPARK_Mode is

   function F (I : Integer) return Boolean with
     Annotate => (GNATprove, Always_Return),
     Post => F'Result and then False;

   type T is not null access function return Integer with
     Post => F (T'Result) and then False;

   function V return Integer is (1);

   function F (I : Integer) return Boolean is
      X : T := V'Access;
   begin
      return I = X.all or else I /= 1;
   end F;

begin
   null;
end;
