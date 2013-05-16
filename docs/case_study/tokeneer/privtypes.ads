------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- PrivTypes
--
-- Description:
--    Types that appear within the context of privileges
--
------------------------------------------------------------------

package PrivTypes
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   type PrivilegeT is (
      UserOnly,
      Guard,
      AuditManager,
      SecurityOfficer
      );

   subtype AdminPrivilegeT is PrivilegeT range Guard .. SecurityOfficer;

   type ClassT is (
      Unmarked,
      Unclassified,
      Restricted,
      Confidential,
      Secret,
      Topsecret
      );

   type ClearanceT is
      record
         Class : ClassT;
      end record;

end PrivTypes;
