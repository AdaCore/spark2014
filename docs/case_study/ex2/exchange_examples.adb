package body Exchange_Examples is

   procedure Exchange (X, Y : in out Integer)
     with Post => (X = Y'Old and Y = X'Old);

   procedure Exchange (X, Y : in out Integer)
   is
      T : Integer;
   begin
      T := X;
      X := Y;
      Y := T;
   end Exchange;

   procedure Exchange_No_Post (X, Y : in out Integer)
   is
      T : Integer;
   begin
      T := X;
      X := Y;
      Y := T;
   end Exchange_No_Post;

   procedure Exchange_No_Post_Unused (X, Y : in out Integer)
   is
      T : Integer;
   begin
      T := X;
      X := Y;
      Y := X;
   end Exchange_No_Post_Unused;

   procedure Exchange_No_Post_Uninitialised (X, Y : in out Integer)
   is
      T : Integer;
   begin
      X := Y;
      Y := T;
   end Exchange_No_Post_Uninitialised;

   procedure Exchange_With_Post_Unused (X, Y : in out Integer)
     with Post => (X = Y'Old and Y = X'Old);

   procedure Exchange_With_Post_Unused (X, Y : in out Integer)
   is
      T : Integer;
   begin
      T := X;
      X := Y;
      Y := X;
   end Exchange_With_Post_Unused;

   procedure Exchange_With_Post_Uninitialised (X, Y : in out Integer)
     with Post => (X = Y'Old and Y = X'Old);

   procedure Exchange_With_Post_Uninitialised (X, Y : in out Integer)
   is
      T : Integer;
   begin
      X := Y;
      Y := T;
   end Exchange_With_Post_Uninitialised;

   procedure Exchange_RTE (X, Y : in out Integer)
     with Pre  => Y < Integer'Last,
          Post => (X = Y'Old and Y = X'Old);

   procedure Exchange_RTE (X, Y : in out Integer)
   is
      T : Integer;
   begin
      T := X + 0;
      X := Y + 2 - 2;
      Y := T;
   end Exchange_RTE;

end Exchange_Examples;
