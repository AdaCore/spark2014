-- Provide an interface to creating flying objects in the simulator
-- $Log: environment.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/11 19:36:35  adi
-- Added Command testpoint
--
-- Revision 1.1  2003/08/11 19:29:37  adi
-- Initial revision
--
--
with Flying_Object;
package body Environment
  --# own state is object_array, item_valid;
is
   subtype Valid_Handle is Handle range 1..Handle'Last;
   type Object is record
      F : Flying_Object.Entity;
      K : Kind;
      R : RCS;
      H : Valid_Handle;
   end record;

   type Object_List is array(Valid_Handle) of Object;
   type Valid_List is array(Valid_Handle) of Boolean;

   Null_Object : constant Object :=
     Object'(F => Flying_Object.Null_Entity,
             K => Cloud,
             R => 1,
             H => Valid_Handle'First);

   Object_Array : Object_List :=
     Object_List'(others => Null_Object);
   Item_Valid : Valid_List :=
     Valid_List'(others => False);

   -- Auxiliary routines
   procedure Find_Slot(H : out Handle)
     --# global in out item_valid;
     --# derives item_valid, H from item_valid;
   is
      Found : Boolean := False;
   begin
      H := 1;
      loop
         --# assert H >= 1 and H <= handle'last;
         if not Item_Valid(H) then
            -- Free slot
            Found := True;
            Item_Valid(H) := True;
         else
            if H = Handle'Last then
               H := Null_Handle;
            else
               H := Handle'Succ(H);
            end if;
         end if;
         exit when Found;
         exit when H = Null_handle;
      end loop;
   end Find_Slot;

   -- Public subroutines

   procedure Add_Object(P : in Cartesian.Position;
                        V : in Cartesian.Velocity;
                        K : in Kind;
                        R : in RCS;
                        H : out Handle)
   --# global in out object_array, item_valid,
   --#   clock.time;
   --# derives
   --#   item_valid from
   --#         * &
   --#   object_array from
   --#         P, V, item_valid, object_array, K, R, clock.time &
   --#   H from
   --#         item_valid &
   --#   clock.time from
   --#         *, item_valid
   --#          ;
   is
      Entity : Flying_Object.Entity;
   begin
      Find_Slot(H);
      if H = Null_Handle then
         -- Can't find a free slot
         null;
      else
         Flying_Object.Create(P => P,
                              V => V,
                              A => Cartesian.Zero_accel,
                              E => Entity);
         Object_Array(H) :=
           Object'(F => Entity,
                   K => K,
                   R => R,
                   H => H);
      end if;
   end Add_Object;


   procedure Set_Object_Position(H : in Handle;
                                 P : in Cartesian.Position)
     --# global in out object_array, clock.time;
     --#        in item_valid;
   --# derives object_array from *, H, P, clock.time, item_valid &
   --#   clock.time from *, H, item_valid;
   is
      Obj : Flying_Object.Entity;
   begin
      if H not in Valid_Handle then
         -- Cannot do anything
         null;
      elsif Item_Valid(H) then
         -- Set position
         Obj := Object_Array(H).F;
         Flying_Object.Set_Position(P => P,
                                    E => Obj);
         Object_Array(H).F := Obj;
      else
         -- No object there
         null;
      end if;
   end Set_Object_Position;

   procedure Get_Object_Position(H : in Handle;
                                 P : out Cartesian.Position)
     --# global in item_valid, object_array;
     --#        in out clock.time;
     --# derives P from H, object_array, item_valid, clock.time &
     --#        clock.time from *, H, item_valid;
   is
      Obj : Object;
   begin
      if H not in Valid_Handle then
         P := Cartesian.Zero_Position;
      elsif Item_Valid(H) then
         Obj := Object_Array(H);
         Flying_Object.Get_Position(E => Obj.F, P => P);
      else
         P := Cartesian.Zero_Position;
      end if;
   end Get_Object_Position;

   procedure Set_Object_Velocity(H : in Handle;
                                 V : in Cartesian.Velocity)
     --# global in out clock.time, object_array;
     --#        in item_valid;
     --# derives object_array from *, H, V, clock.time, item_valid &
     --#        clock.time from *, H, item_valid;
   is
      Obj : Flying_Object.Entity;
   begin
      if H not in Valid_Handle then
         -- Cannot do anything
         null;
      elsif Item_Valid(H) then
         -- Set position
         Obj := Object_Array(H).F;
         Flying_Object.Set_Velocity(V => V,
                                    E => Obj);
         Object_Array(H).F := Obj;
      else
         -- No object there
         null;
      end if;
   end Set_Object_Velocity;


   procedure Get_Object_Velocity(H : in Handle;
                                 V : out Cartesian.Velocity)
   --# global in item_valid, object_array;
   --#        in out clock.time;
   --# derives v from H, item_valid, object_array, clock.time &
   --#        clock.time from *, H, item_valid;
   is
      Obj : Object;
   begin
      if H not in Valid_Handle then
         V := Cartesian.Zero_Velocity;
      elsif Item_Valid(H) then
         Obj := Object_Array(H);
         Flying_Object.Get_Velocity(E => Obj.F, V => V);
      else
         V := Cartesian.Zero_velocity;
      end if;
   end Get_Object_Velocity;


   procedure Set_Object_accel(H : in Handle;
                              A : in Cartesian.Accel)
     --# global in out object_array, clock.time;
     --#        in item_valid;
     --# derives object_array from *, H, A, item_valid, clock.time &
     --#         clock.time from *, H, item_valid;
   is
      Obj : Flying_Object.Entity;
   begin
      if H not in Valid_Handle then
         -- Cannot do anything
         null;
      elsif Item_Valid(H) then
         -- Set position
         Obj := Object_Array(H).F;
         Flying_Object.Set_accel(a => a,
                                 E => Obj);
         Object_Array(H).F := Obj;
      else
         -- No object there
         null;
      end if;
   end Set_Object_Accel;


   procedure Delete_Object(H : in Handle)
   --# global in out item_valid;
   --# derives item_valid from
   --#        item_valid, H;
   is

   begin
      if H not in Valid_Handle then
         -- cannot do anything;
         null;
      elsif Item_Valid(H) then
         -- delete it
         Item_Valid(H) := False;
      else
         -- Already deleted
         null;
      end if;
   end Delete_Object;

   -- testpoint
   procedure Command is separate;

end Environment;
