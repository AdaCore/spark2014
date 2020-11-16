procedure Test_Empty with SPARK_Mode is
    type L_Cell;
    type List is access L_Cell;
    type L_Cell is record
       X : Integer;
       N : List;
    end record;

    function Eq (L1, L2 : access constant L_Cell) return Boolean is
      ((L1 = null) = (L2 = null)
       and then (if L1 /= null then L1.X = L2.X and then Eq (L1.N, L2.N)))
    with Annotate => (GNATprove, Terminating);

    function Deep_Copy (L : access constant L_Cell) return List with
      Volatile_Function,
      Post     => Eq (L, Deep_Copy'Result),
      Annotate => (GNATprove, Terminating)
    is
    begin
       return Copy : List do
          if L /= null then
             declare
                N : constant List := Deep_Copy (L.N);
             begin
                Copy := new L_Cell'(X => L.X, N => N);
             end;
          end if;
       end return;
    end Deep_Copy;

    procedure Update_First (L : not null access L_Cell; I : Integer) with
     -- The call below is in an interferring context!
      Post => L.X = I and Eq (L.N, Deep_Copy (L.N)'Old)
    is
    begin
       L.X := I;
    end Update_First;

    L : List := null;
begin
    L := Deep_Copy (L);
    pragma Assert (L = null);
end Test_Empty;
