package Tictactoe
with SPARK_Mode => On
is

   type Slot is (Empty, Player, Computer);
   type Pos is new Integer range 1 .. 3;
   type Column is array (Pos) of Slot;
   type Board is array (Pos) of Column;

   My_Board : Board := (others => (others => Empty));

   function One_Free_Slot (X, Y : Pos) return Integer is
     (if My_Board(X)(Y) = Empty then 1 else 0);

   function Count_Free_Slots (X, Y : Pos) return Integer is
     (One_Free_Slot(1,1) +
      (if Y >= 2 then One_Free_Slot(1,2) else 0) +
      (if Y >= 3 then One_Free_Slot(1,3) else 0) +
      (if X >= 2 then
         One_Free_Slot(2,1) +
         (if Y >= 2 then One_Free_Slot(2,2) else 0) +
         (if Y >= 3 then One_Free_Slot(2,3) else 0)
       else 0) +
      (if X >= 3 then
         One_Free_Slot(3,1) +
         (if Y >= 2 then One_Free_Slot(3,2) else 0) +
         (if Y >= 3 then One_Free_Slot(3,3) else 0)
       else 0));

   function Num_Free_Slots return Natural is
     (Count_Free_Slots(3,3));

   -- Game operations

   procedure Initialize
     with Post => Num_Free_Slots = 9;

   procedure Player_Play
     with Pre => not Is_Full and Won = Empty,
     Post => Num_Free_Slots = Num_Free_Slots'Old - 1;

   procedure Computer_Play
     with Pre => not Is_Full and Won = Empty,
     Post => Num_Free_Slots = Num_Free_Slots'Old - 1;

   procedure Display;

   function Won return Slot;

   function Is_Full return Boolean is (Num_Free_Slots = 0);

end Tictactoe;
