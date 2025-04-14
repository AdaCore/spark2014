package P is

   subtype Choice is Integer range 1 .. 3;

   subtype Small_Int is Integer range 0 .. 10;

   procedure Proc (J : Choice; K : Small_Int := 0);

end P;
