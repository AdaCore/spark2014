package P is

   type T (Discr : Integer) is null record;

   procedure Proc (Arg : T) with Global => null;

end;
