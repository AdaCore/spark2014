------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 N A M E _ O R D E R E D _ E N T I T I E S                --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2019, AdaCore                       --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

package body Name_Ordered_Entities is

   -----------
   -- First --
   -----------

   function First (Object : Iterator) return Cursor is
   begin
      return (S_Cursor => Object.Container.Variables_Order.First);
   end First;

   --------------
   -- Get_Info --
   --------------

   function Get_Info (Container : Variables_Info;
                      C         : Cursor)
                      return Info is
      C_Map : constant Entity_Infos.Cursor :=
        Container.Variables_Map.Find (Id (C));
   begin
      return (Entity_Infos.Element (C_Map));
   end Get_Info;

   -----------------
   -- Has_Element --
   -----------------

   function Has_Element (Position : Cursor) return Boolean is
   begin
      return Var_Lists.Has_Element (Position.S_Cursor);
   end Has_Element;

   --------------
   -- Has_Info --
   --------------

   function Has_Info (Container : Variables_Info;
                      C         : Cursor)
                      return Boolean is
      C_Map : constant Entity_Infos.Cursor :=
        Entity_Infos.Find (Container.Variables_Map, Id (C));
   begin
      return Entity_Infos.Has_Element (C_Map);
   end Has_Info;

   --------
   -- Id --
   --------

   function Id (C : Cursor)
                return Entity_Id is
   begin
      return Var_Lists.Element (C.S_Cursor).Id;
   end Id;

   -----------------
   -- Insert_Info --
   -----------------

   function Insert_Info (Container : in out Variables_Info;
                         Id        : Entity_Id;
                         Name      : Unbounded_String;
                         C_Info    : Info)
                         return Cursor is
   begin
      if not Container.Variables_Order.Contains ((Id => Id, Name => Name))
      then
         Var_Lists.Include
           (Container.Variables_Order, (Id => Id, Name => Name));
      end if;

      declare
         --  This declare is used to use Insert with 4 arguments which has a
         --  different semantics (wrt assertions) from Insert with 2 arguments.
         Inserted : Boolean;
         C        : Entity_Infos.Cursor;
      begin
         Container.Variables_Map.Insert (Id, C_Info, C, Inserted);
      end;
      return (S_Cursor =>
                Var_Lists.Find
                  (Container.Variables_Order,
                   (Id => Id, Name => Name)));
   end Insert_Info;

   -------------
   -- Iterate --
   -------------

   procedure Iterate
     (Container : Variables_Info;
      Process   : not null access procedure (Position : Cursor))
   is
      Current_Cursor : Cursor :=
        First (Object => (Container => Container'Unrestricted_Access,
                          Position  => null));
   begin
      while Has_Element (Current_Cursor) loop
         Process (Current_Cursor);
         Current_Cursor :=
           Next (Object => (Container => Container'Unrestricted_Access,
                            Position  => null),
                 Position => Current_Cursor);
      end loop;
   end Iterate;

   -------------
   -- Iterate --
   -------------

   function Iterate
     (Container : Variables_Info)
      return Name_Ordered_Iterator_Interfaces.Forward_Iterator'Class is
   begin
      return It : constant Iterator :=
        (Container => Container'Unrestricted_Access,
         Position  => null);
   end Iterate;

   ---------
   -- Key --
   ---------

   function Key (Container : Variables_Info;
                 Position  : Cursor)
                 return Var_Info is
      pragma Unreferenced (Container);
   begin
      return Var_Lists.Element (Position.S_Cursor);
   end Key;

   ------------------
   -- Map_Is_Empty --
   ------------------

   function Map_Is_Empty (Container : Variables_Info)
                          return Boolean is
   begin
      return Container.Variables_Map.Is_Empty;
   end Map_Is_Empty;

   ----------
   -- Name --
   ----------

   function Name (C : Cursor)
                  return Unbounded_String is
   begin
      return Var_Lists.Element (C.S_Cursor).Name;
   end Name;

   ----------
   -- Next --
   ----------

   function Next (Object : Iterator; Position : Cursor) return Cursor is
      pragma Unreferenced (Object);
   begin
      return (S_Cursor => Var_Lists.Next (Position.S_Cursor));
   end Next;

   --------------
   -- Set_Info --
   --------------

   procedure Set_Info (Container : in out Variables_Info;
                       C         : Cursor;
                       C_Info    : Info) is
   begin
      Container.Variables_Map.Include (Id (C), C_Info);
   end Set_Info;

end Name_Ordered_Entities;
