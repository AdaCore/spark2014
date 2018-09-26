------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency.All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd.under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- PrivTypes
--
-- Description:
--    Types that appear within the context of privileges
--
------------------------------------------------------------------

with CommonTypes;

package PrivTypes is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   type PrivilegeT is
     (UserOnly,
      Guard,
      AuditManager,
      SecurityOfficer);

   subtype AdminPrivilegeT is PrivilegeT range Guard..SecurityOfficer;

   type ClassT is
     (Unmarked,
      Unclassified,
      Restricted,
      Confidential,
      Secret,
      Topsecret);

   function ClassT_Image (X : ClassT) return CommonTypes.StringF1L12 is
      (ClassT'Image (X));
   pragma Annotate (GNATprove, False_Positive,
                    "predicate check might fail",
                    "Image of enums of type ClassT are short strings starting at index 1");

   type ClearanceT is record
      Class : ClassT;
   end record;

end PrivTypes;
