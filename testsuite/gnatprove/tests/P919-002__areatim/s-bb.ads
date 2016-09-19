------------------------------------------------------------------------------
--                                                                          --
--                 GNAT RUN-TIME LIBRARY (GNARL) COMPONENTS                 --
--                                                                          --
--                             S Y S T E M . B B                            --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--        Copyright (C) 1999-2002 Universidad Politecnica de Madrid         --
--             Copyright (C) 2003-2004 The European Space Agency            --
--                     Copyright (C) 2003-2011, AdaCore                     --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.                                     --
--                                                                          --
-- You should have received a copy of the GNU General Public License along  --
-- with this library; see the file COPYING3. If not, see:                   --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
-- GNARL was developed by the GNARL team at Florida State University.       --
-- Extensive contributions were provided by Ada Core Technologies, Inc.     --
--                                                                          --
-- The port of GNARL to bare board targets was initially developed by the   --
-- Real-Time Systems Group at the Technical University of Madrid.           --
--                                                                          --
------------------------------------------------------------------------------

--  This is the root package of the bare board implementation of the low level
--  tasking support for Ravenscar compliant run times.

package System.BB is
   pragma Pure;
   pragma No_Elaboration_Code_All;

   --  All of the package specifications in the System.BB hierarchy are system
   --  independent with the exception of the Parameters package which specifies
   --  values of constants describing facts about a given system/architecture,
   --  such as number of interrupt levels or trap vectors. Each box represents
   --  a package specification, with directly below it the main subprograms
   --  provided. Lines indicate a dependency of the upper spec on the lower
   --  one. In addition to the packages listed here, specific ports may define
   --  specifications for functionality unique to each platform, or to factor
   --  out common definitions needed in the implementation.

   --  Most ports will need just two system-specific implementation bodies:

   --     * s-bbcppr.adb: CPU_Primitives body for each CPU architecture

   --     * s-bbbosu.adb: Board_Support body for each supported board

   --   .----------------------------------------------------------.
   --   |          S Y S T E M . O S _ I N T E R F A C E           |
   --   '----------------------------------------------------------'
   --       |              |                              |     |
   --       |              |        .-------------------. |     |
   --       |              |        | BB.Threads.Queues | |     |
   --       |              |        '-------------------' |     |
   --       |              |                Insert        |     |
   --       |              |                Extract       |     |
   --       |              |            Change_Priority   |     |
   --       |              |                   |          |     |
   --       |     .------------------.     .----------------.   |
   --       |     | BB.Board_Support |     |   BB.Threads   |   |
   --       |     '------------------'     '----------------'   |
   --       |       Initialize_Board          Thread_Self       |
   --       |           Set_Alarm             Set_Priority      |
   --       |          Read_Clock             Get_Priority      |
   --       |     Get_Interrupt_Request       Sleep/Wakeup      |
   --       |        |     |     |             |        |       |
   --   .---------------.  |  .-------------------.  .-------------.
   --   | BB.Interrupts |  |  | BB.CPU_Primitives |  |   BB.Time   |
   --   '---------------'  |  '-------------------'  '-------------'
   --    Attach_Handler    |   Context_Switch             Clock
   --   Current_Interrupt  |   Get_Context             Delay_Until
   --                |     |   Set_Context
   --                |     |   Install_Handler
   --                |     |   Disable_Interrupts
   --                |     |   Enable_Interrupts
   --                |     |     |
   --            .-------------------.          .---------------.
   --            |   BB.Parameters   |-.        | BB.Protection |
   --            '-------------------' |-.      '---------------'
   --              '-------------------' |         Enter_Kernel
   --                 '------------------'         Leave_Kernel

end System.BB;
