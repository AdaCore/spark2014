package body Test is

   type Coordinate is record
      X : Integer;
      Y : Integer;
      Z : Integer;
   end record;

   Origin : constant Coordinate := Coordinate'(others => 0);

   type Ammo_Type is (Bullets, Nails, Rockets, Power);

   type Ammo_Store is array (Ammo_Type) of Natural;

   type Player is record
      Position   : Coordinate;
      Look_Yaw   : Integer;
      Look_Pitch : Integer;
      Ammo       : Ammo_Store;
   end record;

   type Player_Id is range 1 .. 8;

   type Players is array (Player_Id range <>) of Player;

   function New_Player_01 return Player is
      P : Player;
   begin
      P := Player'(Position   => (0, 0, 0),
                   Look_Yaw   => 0,
                   Look_Pitch => 0,
                   Ammo       => (others => 0));
      return P;
   end New_Player_01;

   function New_Player_02 return Player is
      P : Player;
   begin
      P.Position   := (0, 0, 0);
      P.Look_Yaw   := 0;
      P.Look_Pitch := 0;
      P.Ammo       := (others => 0);
      return P;
   end New_Player_02;

   function New_Player_03 return Player is
      P : Player;
   begin
      P.Position.X := 0;
      P.Position.Y := 0;
      P.Position.Z := 0;
      P.Look_Yaw   := 0;
      P.Look_Pitch := 0;
      P.Ammo       := (others => 0);
      return P;
   end New_Player_03;

end Test;
