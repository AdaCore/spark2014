package P with
  SPARK_Mode => On
is
   pragma Annotate (GNATprove, External_Axiomatization);

   X : Integer := 0;
end;
