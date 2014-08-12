package Trains with
  SPARK_Mode
is
   --  the railroad is composed of a set of one-way tracks, where each track
   --  joins two locations. A track has a length that is a multiple of an
   --  elementary distance.

   Num_Locations : constant := 5;

   type Location is new Positive range 1 .. Num_Locations;

   type Track is record
      From   : Location;
      To     : Location;
      Length : Positive;
   end record;

   Num_Tracks : constant := 8;

   type Track_Opt_Id is new Natural range 0 .. Num_Tracks;
   subtype Track_Id is Track_Opt_Id range 1 .. Num_Tracks;

   No_Track_Id : constant Track_Opt_Id := 0;

   --  example railroad going around between locations 1 to 5, with additional
   --  tracks from 1 to 3, 2 to 5 and 3 to 5.
   Tracks : constant array (Track_Id) of Track :=
     (1 => (1, 2, 10),
      2 => (1, 3, 10),
      3 => (2, 3, 10),
      4 => (2, 5, 10),
      5 => (3, 4, 10),
      6 => (3, 5, 10),
      7 => (4, 5, 10),
      8 => (5, 1, 10));

   --  the map of previous tracks records for each location the tracks that
   --  precede it. This information should be consistent with the one in
   --  Tracks.

   Max_Num_Previous_Tracks : constant := 3;

   type Prev_Id is range 1 .. Max_Num_Previous_Tracks;
   type Track_Ids is array (Prev_Id) of Track_Opt_Id;

   Previous_Tracks : constant array (Location) of Track_Ids :=
     (1 => (8, 0, 0),
      2 => (1, 0, 0),
      3 => (2, 3, 0),
      4 => (5, 0, 0),
      5 => (4, 6, 7));

   --  the railroad should respect the property that no track precedes itself

   function No_Track_Precedes_Itself return Boolean is
      (for all Track in Track_Id =>
          (for all Id in Prev_Id =>
              Previous_Tracks (Tracks (Track).From) (Id) /= Track));

   --  a train is identified by its unique identifier. The position of each
   --  train is given by the starting track it's in (Track_Begin) and the
   --  position in this track (Pos_Begin), with the ending track it's in
   --  (Track_End) which can be the same as the starting track. A train
   --  can never be on three tracks.

   Max_Num_Trains : constant := 10;

   type Train_Id is new Positive range 1 .. Max_Num_Trains;

   type Train_Position is record
      Track_Begin : Track_Id;
      Pos_Begin   : Natural;
      Track_End   : Track_Id;
   end record;

   Cur_Num_Trains : Train_Id;

   Trains : array (Train_Id) of Train_Position;

   function Entering_A_Track (Position : Train_Position) return Boolean is
      (Position.Track_Begin /= Position.Track_End and then
       (for some Id in Prev_Id =>
          Position.Track_End = Previous_Tracks (Tracks (Position.Track_Begin).From) (Id)));

   function Inside_A_Track (Position : Train_Position) return Boolean is
      (Position.Track_Begin = Position.Track_End);

   --  it should always hold that there is at most one train in every track
   --  segment

   function One_Train_At_Most_Per_Track return Boolean is
      (for all Train in Train_Id range 1 .. Cur_Num_Trains =>
         (for all Other_Train in Train_Id range 1 .. Cur_Num_Trains =>
             (if Other_Train /= Train then
                Trains (Train).Track_Begin /= Trains (Other_Train).Track_Begin and then
                Trains (Train).Track_Begin /= Trains (Other_Train).Track_End and then
                Trains (Train).Track_End   /= Trains (Other_Train).Track_Begin and then
                Trains (Train).Track_End   /= Trains (Other_Train).Track_End)));

   --  at each instant, the behavior of the train depends on the value of the
   --  signal on the track it's in and on the track ahead

   type Signal is (Green, Orange, Red);

   Track_Signals : array (Track_Id) of Signal;

   --  the signal should be Red on every track on which there is a train, and
   --  Orange on every previous track, unless already Red on that track.

   function Occupied_Tracks_On_Red return Boolean is
      (for all Train in Train_Id range 1 .. Cur_Num_Trains =>
         Track_Signals (Trains (Train).Track_Begin) = Red and then
         Track_Signals (Trains (Train).Track_End) = Red);

   --  Return the Id'th track that precedes the ending track of the train
   function Get_Previous_Track
     (Position : Train_Position;
      Id       : Prev_Id) return Track_Opt_Id
   is
      (Previous_Tracks (Tracks (Position.Track_End).From) (Id));

   --  Return the Id'th track that precedes the starting track of the train,
   --  provided it is different from the ending track of the train
   function Get_Other_Previous_Track
     (Position : Train_Position;
      Id       : Prev_Id) return Track_Opt_Id
   is
      (if Previous_Tracks (Tracks (Position.Track_Begin).From) (Id) =
           Position.Track_End
       then
          No_Track_Id
       else
          Previous_Tracks (Tracks (Position.Track_Begin).From) (Id));

   function Is_Previous_Track
     (Position : Train_Position;
      Track    : Track_Id) return Boolean
   is
      (for some Id in Prev_Id =>
         Track = Get_Previous_Track (Position, Id)
           or else
         Track = Get_Other_Previous_Track (Position, Id));

   function Previous_Tracks_On_Orange_Or_Red return Boolean is
      (for all Train in Train_Id range 1 .. Cur_Num_Trains =>
         (for all Id in Prev_Id =>
            (if Get_Previous_Track (Trains (Train), Id) /= No_Track_Id then
               Track_Signals (Get_Previous_Track (Trains (Train), Id)) in
                 Orange | Red)
              and then
            (if Get_Other_Previous_Track (Trains (Train), Id) /= No_Track_Id then
               Track_Signals (Get_Other_Previous_Track (Trains (Train), Id)) in
                 Orange | Red)));

   function Safe_Signaling return Boolean is
      (Occupied_Tracks_On_Red and then
       Previous_Tracks_On_Orange_Or_Red);

   --  valid movements of trains can be of 3 kinds:
   --    . moving inside one or two tracks
   --    . entering a new track
   --    . leaving a track

   --  The following functions correspond each to one of these kinds of
   --  movements. Function Valid_Move returns whether a movement is among
   --  these 3 kinds.

   function Moving_Inside_Current_Tracks
     (Cur_Position : Train_Position;
      New_Position : Train_Position) return Boolean
   is
      (Cur_Position.Track_Begin = New_Position.Track_Begin and then
       Cur_Position.Track_End = New_Position.Track_End);

   function Moving_To_A_New_Track
     (Cur_Position : Train_Position;
      New_Position : Train_Position) return Boolean
   is
      (Inside_A_Track (Cur_Position) and then
       Entering_A_Track (New_Position) and then
       Cur_Position.Track_Begin = New_Position.Track_End);

   function Moving_Away_From_Current_Track
     (Cur_Position : Train_Position;
      New_Position : Train_Position) return Boolean
   is
      (Entering_A_Track (Cur_Position) and then
       Inside_A_Track (New_Position) and then
       Cur_Position.Track_Begin = New_Position.Track_End);

   function Valid_Move
     (Cur_Position : Train_Position;
      New_Position : Train_Position) return Boolean
   is
      --  either the train keeps moving in the current tracks
      (Moving_Inside_Current_Tracks (Cur_Position, New_Position)
         or else
      --  or the train was inside a track and enters a new track
       Moving_To_A_New_Track (Cur_Position, New_Position)
         or else
      --  or the train was entering a track and leaves the previous one
       Moving_Away_From_Current_Track (Cur_Position, New_Position));

   --  moving the train ahead along a valid movement can result in:
   --    . Full_Speed: the movement was performed, the position of the train
   --                  (Trains) and the signals (Track_Signals) have been
   --                  updated, and the train can continue full speed.
   --    . Slow_Down:  Same as Full_Speed, but the train is entering an Orange
   --                  track and should slow down.
   --    . Keep_Going: Same as Full_Speed, but the train should keep its
   --                  current speed.
   --    . Stop:       No movement performed, the train should stop here,
   --                  prior to entering a Red track.

   type Move_Result is (Full_Speed, Slow_Down, Keep_Going, Stop);

   procedure Move
     (Train        : Train_Id;
      New_Position : Train_Position;
      Result       : out Move_Result)
   with
     Global => (Input  => Cur_Num_Trains,
                In_Out => (Trains, Track_Signals)),
     Pre  => Train in 1 .. Cur_Num_Trains and then
             Valid_Move (Trains (Train), New_Position) and then
             One_Train_At_Most_Per_Track and then
             Safe_Signaling,
     Post => One_Train_At_Most_Per_Track and then
             Safe_Signaling;

end Trains;
