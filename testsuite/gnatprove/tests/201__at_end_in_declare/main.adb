procedure Main with SPARK_Mode is
   function At_End (X : access constant Integer)
                    return access constant Integer is (X)
     with Ghost, Global => null, Annotate => (GNATprove , At_End_Borrow);
   procedure Test (X : not null access Integer) is
      Y : not null access Integer := X;
   begin
      pragma Assert (declare
                        J : constant Integer := At_End (X).all;
                     begin
                        J = At_End (Y).all
                     );
   end;
begin
   null;
end Main;
