procedure Bad_Moves_Of_Deep with SPARK_Mode is
   type Int_Ptr is access all Integer;
   type R is record
      F : Int_Ptr;
      G : aliased Integer;
   end record;

   X : Int_Ptr := new Integer'(10);
   Y : Int_Ptr := X.all'Access;

   procedure Bad_1 with Global => null is
      type Loc_Int_Ptr is access all Integer;
      X : R := (G => 1, F => new Integer'(10));
      Y : Loc_Int_Ptr := X.G'Access;
   begin
      pragma Assert (X.F.all = 10);
      pragma Assert (X.G = 10);             -- Error, X.G is moved
      X.F.all := 15;
      X.G := 15;                            -- Error, X.G is moved
      X := (G => 1, F => new Integer'(10)); -- Error, X.G is moved
   end Bad_1;

   procedure Bad_2 with Global => null is
      type Loc_Int_Ptr is access all Integer;
      type Rec_Arr is array (Positive range 1 .. 2) of R;
      X : Rec_Arr := (1 => (G => 1, F => new Integer'(10)),
                      2 => (G => 1, F => new Integer'(10)));
      Y : Loc_Int_Ptr := X (1).G'Access;
   begin
      pragma Assert (X (1).F.all = 10);
      pragma Assert (X (1).G = 10);               -- Error, X (1).G is moved
      X (1).F.all := 15;
      X (1).G := 15;                              -- Error, X (1).G is moved
      pragma Assert (X (2).F.all = 10);
      pragma Assert (X (2).G = 10);               -- Error, X (?).G is moved
      X (2).F.all := 15;
      X (2).G := 15;                              -- Error, X (?).G is moved
      X := (1 => (G => 1, F => new Integer'(10)), -- Error, X (1).G is moved
            2 => (G => 1, F => new Integer'(10)));
   end Bad_2;

   procedure Bad_3 with Global => null is
      X : R := (G => 1, F => new Integer'(10));
      Y : Int_Ptr := X.F.all'Access;
   begin
      pragma Assert (X.F.all = 10);         -- Error, X.F.all is moved
      pragma Assert (X.G = 10);
      X.F.all := 15;                        -- Error, X.F.all is moved
      X.G := 15;
      X.F := new Integer'(15);
   end Bad_3;

   procedure Bad_4 with Global => null is
      type Rec_Arr is array (Positive range 1 .. 2) of R;
      X : Rec_Arr := (1 => (G => 1, F => new Integer'(10)),
                      2 => (G => 1, F => new Integer'(10)));
      Y : Int_Ptr := X (1).F.all'Access;
   begin
      pragma Assert (X (1).F.all = 10);           -- Error, X (1).F.all is moved
      pragma Assert (X (1).G = 10);
      X (1).F.all := 15;                          -- Error, X (1).F.all is moved
      X (1).G := 15;
      X (1).F := new Integer'(15);
      pragma Assert (X (2).F.all = 10);           -- Error, X (?).F.all is moved
      pragma Assert (X (2).G = 10);
      X (2).F.all := 15;                          -- Error, X (?).F.all is moved
      X (2).G := 15;
      X (2).F := new Integer'(15);
      X := (1 => (G => 1, F => new Integer'(10)),
            2 => (G => 1, F => new Integer'(10)));
   end Bad_4;

   procedure Bad_5 with Global => null is
      type Loc_Int_Ptr is access all R;
      X : aliased R := (G => 1, F => new Integer'(10));
      Y : Loc_Int_Ptr := X'Access;
   begin
      pragma Assert (X.F.all = 10);         -- Error, X is moved
      pragma Assert (X.G = 10);             -- Error, X is moved
      X.F.all := 15;                        -- Error, X is moved
      X.G := 15;                            -- Error, X is moved
      X := (G => 1, F => new Integer'(10)); -- Error, X is moved
   end Bad_5;

   function Get return Int_Ptr is -- Error, X is moved on return
     (X.all'Access);
begin
   Y.all := 12;
   pragma Assert (X.all = 10); -- Error, X is moved
   X.all := 15;                -- Error, X is moved
end Bad_Moves_Of_Deep;
