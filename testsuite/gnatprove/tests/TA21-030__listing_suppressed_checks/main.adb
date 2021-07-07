with P; --  P is SPARK_Mode => On; P.Inner is separate and explicitly SPARK_Mode => Off
with Q; --  SPARK_Mode is not explicitly specified for these Q packages
with Q2;
with Q3;

procedure Main
  with SPARK_Mode => On
is
    Foo : Integer;
begin
    Foo := P.Assume_Natural (-1); --  Has pragma Assume (X in Natural)
    P.Annotate_Intentional (True); --  Justifies uninitialised variables
    Q (Foo);
    Q2;
    Q3;
end Main;
