procedure Concat is
    subtype Index is Integer range 1 .. 10;
    type T is array (Index) of Boolean;
    X : T := (others => True) ;
    Y : T := X (6 .. 10) & X (1 .. 5);
begin
   null;
end Concat;
