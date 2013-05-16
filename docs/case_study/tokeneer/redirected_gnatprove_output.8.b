Phase 1 of 3: frame condition computation ...
Phase 2 of 3: translation to intermediate language ...
Statistics logged in gnatprove.out
(detailed info can be found in /home/pavlos/Documents/Versioning_systems/Subversion/hi-lite/case_studies/tokeneer/gnatprove/*.alfa)
Phase 3 of 3: generation and proof of VCs ...
analyzing AuditLog.NextListIndex, 1 checks
auditlog.adb:57:26: info: range check proved
analyzing AuditLog.CheckLogAlarm, 0 checks
analyzing AuditLog.ConvertToAuditDescription, 1 checks
auditlog.adb:100:39: info: range check proved
analyzing AuditLog.DeleteArchiveFile, 1 checks
auditlog.adb:354:22: precondition not proved
analyzing AuditLog.DeleteLogFile, 0 checks
analyzing AuditLog.AddElementToFile, 0 checks
analyzing AuditLog.AddElementToFile.NameOfType, 0 checks
analyzing AuditLog.AddElementToLogFile, 8 checks
auditlog.adb:570:44: info: range check proved
auditlog.adb:570:47: info: overflow check proved
auditlog.adb:570:66: info: overflow check proved
auditlog.adb:575:65: postcondition not proved
auditlog.adb:796:10: info: precondition proved
auditlog.adb:805:10: info: assertion proved
auditlog.adb:807:10: info: precondition proved
auditlog.adb:814:44: info: range check proved
analyzing precondition for AuditLog.AddElementToLogFile, 3 checks
auditlog.adb:566:44: info: range check proved
auditlog.adb:566:47: info: overflow check proved
auditlog.adb:566:66: info: overflow check proved
analyzing AuditLog.AddElementToLogFile.AddElementToCurrentFile, 2 checks
auditlog.adb:647:41: info: postcondition proved
auditlog.adb:687:75: info: range check proved
analyzing precondition for AuditLog.AddElementToLogFile.AddElementToCurrentFile, 0 checks
analyzing AuditLog.AddElementToLogFile.AddElementToNextFile, 2 checks
auditlog.adb:707:60: info: postcondition proved
auditlog.adb:771:53: info: range check proved
analyzing precondition for AuditLog.AddElementToLogFile.AddElementToNextFile, 0 checks
analyzing AuditLog.AddElementToLogFile.AddElementToNextFile.SetCurrentFileToNextFreeFile, 2 checks
auditlog.adb:753:16: info: loop invariant initialization proved
auditlog.adb:753:16: info: loop invariant preservation proved
analyzing AuditLog.TruncateLog, 4 checks
auditlog.adb:834:52: info: postcondition proved
auditlog.adb:836:44: info: overflow check proved
auditlog.adb:882:50: info: range check proved
auditlog.adb:884:44: info: range check proved
analyzing precondition for AuditLog.TruncateLog, 1 checks
auditlog.adb:832:44: info: overflow check proved
analyzing AuditLog.AddElementToLogFileWithTruncateChecks, 19 checks
auditlog.adb:914:32: info: postcondition proved
auditlog.adb:916:44: info: range check proved
auditlog.adb:916:47: info: overflow check proved
auditlog.adb:916:66: info: overflow check proved
auditlog.adb:968:10: info: precondition proved
auditlog.adb:975:10: assertion not proved
auditlog.adb:977:50: info: range check proved
auditlog.adb:977:53: info: overflow check proved
auditlog.adb:977:72: info: overflow check proved
auditlog.adb:982:10: info: precondition proved
auditlog.adb:993:10: info: assertion proved
auditlog.adb:995:50: info: range check proved
auditlog.adb:995:53: info: overflow check proved
auditlog.adb:995:72: info: overflow check proved
auditlog.adb:1007:7: info: assertion proved
auditlog.adb:1009:47: info: range check proved
auditlog.adb:1009:50: info: overflow check proved
auditlog.adb:1009:69: info: overflow check proved
auditlog.adb:1014:7: precondition not proved
analyzing precondition for AuditLog.AddElementToLogFileWithTruncateChecks, 3 checks
auditlog.adb:911:44: info: range check proved
auditlog.adb:911:47: info: overflow check proved
auditlog.adb:911:66: info: overflow check proved
analyzing AuditLog.AddElementToLog, 7 checks
auditlog.adb:1383:14: info: range check proved
auditlog.adb:1438:7: info: precondition proved
auditlog.adb:1448:10: info: precondition proved
auditlog.ads:234:32: info: postcondition proved
auditlog.ads:236:44: info: range check proved
auditlog.ads:236:47: info: overflow check proved
auditlog.ads:236:66: info: overflow check proved
analyzing precondition for AuditLog.AddElementToLog, 3 checks
auditlog.ads:231:44: info: range check proved
auditlog.ads:231:47: info: overflow check proved
auditlog.ads:231:66: info: overflow check proved
analyzing AuditLog.ArchiveLog, 17 checks
auditlog.adb:1521:22: precondition not proved
auditlog.adb:1560:13: info: loop invariant initialization proved
auditlog.adb:1560:13: info: loop invariant preservation proved
auditlog.adb:1565:53: info: range check proved
auditlog.adb:1565:56: info: overflow check proved
auditlog.adb:1565:75: info: overflow check proved
auditlog.adb:1595:52: info: range check proved
auditlog.adb:1605:7: info: assertion proved
auditlog.adb:1607:47: info: range check proved
auditlog.adb:1607:50: info: overflow check proved
auditlog.adb:1607:69: info: overflow check proved
auditlog.adb:1611:10: info: precondition proved
auditlog.adb:1621:7: info: precondition proved
auditlog.ads:271:32: info: postcondition proved
auditlog.ads:273:44: info: range check proved
auditlog.ads:273:47: info: overflow check proved
auditlog.ads:273:66: info: overflow check proved
analyzing precondition for AuditLog.ArchiveLog, 3 checks
auditlog.ads:268:44: info: range check proved
auditlog.ads:268:47: info: overflow check proved
auditlog.ads:268:66: info: overflow check proved
analyzing AuditLog.ClearLogEntries, 21 checks
auditlog.adb:1688:10: info: loop invariant initialization proved
auditlog.adb:1688:10: loop invariant preservation not proved
auditlog.adb:1691:50: info: range check proved
auditlog.adb:1691:53: info: overflow check proved
auditlog.adb:1691:72: info: overflow check proved
auditlog.adb:1701:10: info: loop invariant proved
auditlog.adb:1706:50: info: range check proved
auditlog.adb:1706:53: info: overflow check proved
auditlog.adb:1706:72: info: overflow check proved
auditlog.adb:1712:53: info: range check proved
auditlog.adb:1715:47: info: range check proved
auditlog.adb:1722:7: assertion not proved, requires NumberLogEntries = LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries + LogFileEntries(CurrentLogFile)
auditlog.adb:1724:47: info: range check proved
auditlog.adb:1724:50: info: overflow check proved
auditlog.adb:1724:69: info: overflow check proved
auditlog.adb:1735:10: precondition not proved
auditlog.adb:1743:7: precondition not proved
auditlog.ads:305:32: info: postcondition proved
auditlog.ads:307:44: info: range check proved
auditlog.ads:307:47: info: overflow check proved
auditlog.ads:307:66: info: overflow check proved
analyzing precondition for AuditLog.ClearLogEntries, 3 checks
auditlog.ads:302:44: info: range check proved
auditlog.ads:302:47: info: overflow check proved
auditlog.ads:302:66: info: overflow check proved
analyzing AuditLog.CancelArchive, 2 checks
auditlog.adb:1768:10: info: loop invariant initialization proved
auditlog.adb:1768:10: info: loop invariant preservation proved
analyzing AuditLog.TheAuditAlarm, 0 checks
analyzing AuditLog.SystemFaultOccurred, 0 checks

