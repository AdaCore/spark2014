procedure Test with SPARK_Mode is
   procedure A with Import, Global => null;
   procedure B with Import, Global => null;
   pragma Annotate (GNATprove, Always_Return, B);
   pragma Annotate (GNATprove, Always_Return, A);

   procedure C with Import, Global => null;
   package D is
      pragma Annotate (GNATprove, Always_Return, D);
   end D;
   pragma Annotate (GNATprove, Always_Return, C);
   procedure E with Import, Global => null;
   pragma Annotate (GNATprove, Always_Return, D);
begin
   null;
end Test;
