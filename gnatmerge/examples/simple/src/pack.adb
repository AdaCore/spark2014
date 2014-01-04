--
--  Copyright (C) 2011-2014, AdaCore
--
--
--

package body Pack is
   --

   function P1 (X : Integer) return Integer is
   begin
      return X + 1;
   end P1;

   --
   --
   --
   --

   function P2 (X : Integer) return Integer is
   begin
      return X + 2;
   end P2;

   --
   --
   --
   --

   function P3 (X : Integer) return Integer is
   begin
      return X + 3;
   end P3;

   --
   --
   --
   --

   function P4 (X : Integer) return Integer is
   begin
      return X + 4;
   end P4;

   --
   --
   --
   --

   procedure P5 is
   begin
      null;
   end P5;

   --
   --
   --
   --

   procedure P6 is
   begin
      null;
   end P6;

end Pack;
