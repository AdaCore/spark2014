-- Implement flying object tracking
-- $Log: flying_object.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/11 19:24:52  adi
-- Time-extrapolate position and velocity on read
--
-- Revision 1.1  2003/08/11 18:02:27  adi
-- Initial revision
--
--
with Systemtypes;
package body Flying_Object is
   subtype Integer32 is Systemtypes.Integer32;

   procedure Extrapolate_Position(T : in Clock.Millisecond;
                                  E : in Entity;
                                  P : out Cartesian.Position)
     --# derives P from T,E;
   is
      T_Offset, T_O_squared : Integer32;
      D_Distance : Measuretypes.Meter;

      procedure Extrapolate_Linear(U : in Measuretypes.Meter_Per_Sec;
                                   A : in Measuretypes.Cm_Per_Sec_2;
                                   S : out Measuretypes.Meter)
        --# global in T_Offset, T_O_Squared;
        --# derives S from U, A, T_Offset, T_O_Squared;
      is begin
         S := Measuretypes.Meter(Integer32(U) * T_Offset +
                                (Integer32(A)*T_O_Squared)/2);
      end Extrapolate_Linear;

   begin
      -- Calculate the time offset
      T_Offset := Integer32(T) - Integer32(E.T);
      T_O_Squared := T_Offset * T_Offset;
      -- Where A is constant, s = ut + at^2 / 2
      Extrapolate_Linear(U => E.V.Vx,
                         A => E.A.Ax,
                         S => D_Distance);
      P.X := D_Distance + E.P.X;
      Extrapolate_Linear(U => E.V.Vy,
                         A => E.A.Ay,
                         S => D_Distance);
      P.y := D_Distance + E.P.y;
      Extrapolate_Linear(U => E.V.Vz,
                         A => E.A.Az,
                         S => D_Distance);
      P.z := D_Distance + E.P.z;
   end Extrapolate_Position;

   procedure Extrapolate_Velocity(T : in Clock.Millisecond;
                                  E : in Entity;
                                  V : out Cartesian.Velocity)
   --# derives V from T, E;
   is
      T_Offset : Integer32;
   begin
      T_Offset := Integer32(T) - Integer32(E.T);
      -- v = u + at
      V.Vx := E.V.Vx + Measuretypes.Meter_Per_Sec
        (Integer32(E.A.Ax) * T_Offset);
      V.Vy := E.V.Vy + Measuretypes.Meter_Per_Sec
        (Integer32(E.A.Ay) * T_Offset);
      V.Vz := E.V.Vz + Measuretypes.Meter_Per_Sec
        (Integer32(E.A.Az) * T_Offset);
   end Extrapolate_Velocity;

   procedure Create(P : in Cartesian.Position;
                    V : in Cartesian.Velocity;
                    A : in Cartesian.Accel;
                    E : out Entity)
   is
      T : Clock.Millisecond;
      Valid : Boolean;
   begin
      Clock.Read(T => T,
                 Valid => Valid);
      if Valid then
         E := Entity'(P => P,
                      V => V,
                      A => A,
                      T => T);
      else
         E := Entity'(P => Cartesian.Zero_Position,
                      V => Cartesian.Zero_Velocity,
                      A => Cartesian.Zero_Accel,
                      T => 0);
      end if;
   end Create;


   procedure Set_Position(P : in Cartesian.Position;
                          E : in out Entity)
   is
      T : Clock.Millisecond;
      Valid : Boolean;
      New_V : Cartesian.Velocity;
   begin
      -- Set the position and extrapolate the velocity to the
      --  current time
      Clock.Read(T => T,
                 Valid => Valid);
      if Valid then
         Extrapolate_Velocity(T => T,
                              E => E,
                              V => New_V);
         E.V := New_V;
         -- Change the position to the p
         E.P := P;
         -- Leave accel alone;
         -- Update the last time marker
         E.T := T;
      else
         E.P := P;
         E.T := 0;
         -- Leave velocity and accel alone
      end if;
   end Set_Position;

   procedure Get_Position(E : in Entity;
                          P : out Cartesian.Position)
   is
      T : Clock.Millisecond;
      Valid : Boolean;
   begin
      Clock.read(T => T,
                 Valid => Valid);
      if Valid then
         Extrapolate_Position(T => T,
                              E => E,
                              P => P);
      else
         P := E.P;
      end if;
   end Get_Position;

   procedure Set_Velocity(V : in Cartesian.Velocity;
                          E : in out Entity)
   is
      T : Clock.Millisecond;
      Valid : Boolean;
      New_P : Cartesian.Position;
   begin
      Clock.Read(T => T,
                 Valid => Valid);
      if Valid then
         -- Extrapolate position to current point
         Extrapolate_Position(T => T,
                              E => E,
                              P => New_P);
         E.P := New_P;
         E.V := V;
         E.T := T;
         -- leave accel alone
      else
         -- Can't extrapolate position, just change velocity
         E.V := V;
         E.T := 0;
      end if;
   end Set_Velocity;

   procedure Get_Velocity(E : in Entity;
                          V  : out Cartesian.Velocity)
   is
      T : Clock.Millisecond;
      Valid : Boolean;
   begin
      Clock.read(T => T,
                 Valid => Valid);
      if Valid then
         Extrapolate_velocity(T => T,
                              E => E,
                              V => V);
      else
         V := E.V;
      end if;
   end Get_Velocity;


   procedure Set_accel(A : in Cartesian.Accel;
                       E : in out Entity)
   is
      T : Clock.Millisecond;
      Valid : Boolean;
      New_P : Cartesian.Position;
      New_V : Cartesian.Velocity;
   begin
      Clock.Read(T => T,
                 Valid => Valid);
      if Valid then
         -- Extrapolate position and velocity to date
         Extrapolate_Position(T => T,
                              E => E,
                              P => New_P);
         Extrapolate_velocity(T => T,
                              E => E,
                              V => New_v);
         E := Entity'(P => New_P,
                      V => New_V,
                      A => A,
                      T => T);
      else
         E.A := A;
         E.T := 0;
         -- Leave position and velocity alone
      end if;
   end Set_Accel;

   procedure Get_accel(E : in Entity;
                       A  : out Cartesian.accel)
   is
   begin
      A := E.A;
   end Get_Accel;

end Flying_Object;



