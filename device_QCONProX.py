# name=ICON QCON Pro X
# url= https://forum.image-line.com/viewtopic.php?f=1994&t=254916#p1607888
# supportedDevices=ICON QCON Pro X
# Based on the ImageLine default Mackie script (refactored for the ICON QCON Pro X)
#
# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# Includes the following additional features:
# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# Support for the second screen
# Support for the Stereo Master Meters
# Support for the FL Studio Overlay (firmware 2)
# Option to always default Jog Dial to the playlist (song pointer)
# Option to display Track Numbers (default) or expanded TrackNames over 2 rows on the first screen
# Dynamic Channel (Track) numbers shown on second screen
# Dynamic Bank numbers shown on second screen
# Full selected Track name shown on second screen
# Current assignment information shown on second screen
# All temporary messages defaulted to the second screen 
# Added options for Mixer Colouring (+reset to default)
# Added feedback (where possible) for all operations onto the second screen
# Added support to reset all tracks to "un-muted" (with a single operation)
# Added support to disarm all tracks (with a single operation)
# Added 4 options for "Free Control" parameter naming choices
# Added comment headers to asist with script readability
# Added parameter value nanmesfor EQ Assignment (relating to default FL Studio Mixer parametric EQ)
# Option added for EQ Assignment to "Reset all"

import time
import arrangement
import channels
import device
import general
import launchMapPages
import math
import midi
import mixer
import patterns
import playlist
import plugins
import transport
import ui
import utils

MackieCU_KnobOffOnT = [(midi.MIDI_CONTROLCHANGE + (1 << 6)) << 16,
                       midi.MIDI_CONTROLCHANGE + ((0xB + (2 << 4) + (1 << 6)) << 16)]
MackieCU_nFreeTracks = 64

# -----------------
# STATIC VARIABLES
# -----------------
# Mackie CU pages
MackieCUPage_Pan = 0
MackieCUPage_Stereo = 1
MackieCUPage_Sends = 2
MackieCUPage_FX = 3
MackieCUPage_EQ = 4
MackieCUPage_Free = 5

ExtenderLeft = 0
ExtenderRight = 1

OffOnStr = ('off', 'on')
MasterPeak = 0
BankingColours = [-22508, -15461356, -14397697, -60167, -98028, -1768, -8126692, -14617601, -2479873, -54171, -52992, -98028]
TrackColours = [ -4930828, -16777216, -14737633, -12632257, -10526881,-8421505, -6316129, -4210753,
                -12037802, -251649, -244993, -238081, -165633, -158721, -151809, -79361, -72449, -16382223, -14605838, -12763660,-10921483, -9079305, -7302919, -5460742,
                 -3618564, -34560, -30692, -26567, -22442, -18317, -14193, -10068, -5943, -2555897, -2286810,-1952187, -1617564, -1282941, -1013854, -679231,
                 -344608, -16763645, -15118819, -13408457, -11763631, -10053013, -8408187, -6697825,-5052999, -13608273, -12425032, -11175998, -9926964, -8677930, -7428896, -6179862,
                 -2105377, -13762559, -12052197, -10341834, -8631472, -6920853, -5210490, -3500128,
                 -1789765, -1119232, -1053161,-987090, -921019, -854692, -788621, -722550, -656479, -22508, -15461356, -14397697, -60167, -98028, -1768, -8126692,
                 -14617601, -2479873, -54171, -52992, -98028,-12037802, -251649, -244993, -238081, -165633, -158721, -151809, -79361, -72449, -16382223, -14605838,
                 -12763660, -10921483, -9079305, -7302919, -5460742, -3618564,-34560, -30692, -26567, -22442, -18317, -14193, -10068, -5943, -2555897, -2286810,
                 -1952187, -1617564, -1282941, -1013854, -679231, -344608, -16763645, -15118819, -13408457,
                -11763631, -10053013, -8408187, -6697825, -5052999, -13608273, -12425032, -11175998, -9926964, -8677930, -7428896, -6179862, -4930828, -16777216, -14737633, -12632257, -10526881,
                -8421505, -6316129, -4210753, -2105377, -13762559, -12052197, -10341834, -8631472, -6920853, -5210490, -3500128, -1789765, -1119232, -1053161, -987090, -921019, -854692, -788621, -722550,
                -656479, -22508, -15461356, -14397697, -60167, -98028, -1768, -8126692, -14617601, -2479873, -54171, -52992, -98028]
debug = True

#################################
# CLASS FOR COLUMN RELATED ITEMS
#################################

class TMackieCol:
    def __init__(self):
        self.TrackNum = 0
        self.BaseEventID = 0
        self.KnobEventID = 0
        self.KnobPressEventID = 0
        self.KnobResetEventID = 0
        self.KnobResetValue = 0
        self.KnobMode = 0 #[0=default], [1=parameter, pan, volume, off],[2=self.Flip],[3=centered?],[4=?]
        self.KnobCenter = 0
        self.SliderEventID = 0
        self.Peak = 0
        self.Tag = 0
        self.SliderName = ""
        self.KnobName = ""
        self.LastValueIndex = 0
        self.ZPeak = False
        self.Dirty = False
        self.KnobHeld = False

##################################
# CLASS FOR GENERAL FUNCTIONALITY
##################################

class TMackieCU():
    def __init__(self):
        self.LastMsgLen = 0x37
        self.TempMsgT = ["", ""]
        self.LastTimeMsg = bytearray(10)
        self.Shift = False
        self.Control = False
        self.Option = False
        self.Alt = False
        self.TempMsgDirty = False
        self.JogSource = 0
        self.TempMsgCount = 0
        self.SliderHoldCount = 0
        self.FirstTrack = 0
        self.FirstTrackT = [0, 0]
        self.ColT = [0 for x in range(9)]
        for x in range(0, 9):
            self.ColT[x] = TMackieCol()
        self.FreeCtrlT = [0 for x in range(
            MackieCU_nFreeTracks - 1 + 2)]  # 64+1 sliders
        self.Clicking = False
        self.Scrub = False
        self.Flip = False
        self.MeterMode = 1  # enabled!
        self.CurMeterMode = 0
        self.Page = 0
        self.SmoothSpeed = 0
        self.MeterMax = 0
        self.ActivityMax = 0
        self.DefaultJogToPlaylist = False
        self.MixerScroll = False
        self.MackieCU_PageNameT = ('Panning                          (press VPOTS to reset)', 'Stereo Separation               (press VPOTS to reset)', '" - press VPOTS to enable',
                                   '" - turn VPOTS to adjust', '" - press VPOTS to reset',  '(Free Controls)')
        self.MackieCU_MeterModeNameT = ('Meters Disabled', 'Meters Enabled')
        self.MackieCU_ExtenderPosT = ('left', 'right')
        self.FreeEventID = 400
        self.ArrowsStr = chr(0x7F) + chr(0x7E) + chr(0x32)
        self.AlphaTrack_SliderMax = round(13072 * 16000 / 12800)
        self.ExtenderPos = ExtenderLeft
        self.CurPluginID = -1
        self.LCD1 = bytearray([0xF0, 0x00, 0x00, 0x66, 0x14, 0x12, 0])
        self.LCD2 = bytearray([0xF0, 0x00, 0x00, 0x67, 0x15, 0x13, 0])
        self.MasterPeak = 0
        self.Msg1 = ''
        self.Msg2 = ''
        self.ShowTrackNumbers = True
        self.FreeText = 0  # Zenology - change to 1 (generic) or -1 (blank)
        self.colourOptions = 0

# -------------------------------------------------------------------------------------------------------------------------------
# FUNCTIONS:
# -------------------------------------------------------------------------------------------------------------------------------

    #############################################################################################################################
    #                                                                                                                           #
    # REMOVE CARRIAGE RETURNS & LINEFEEDS CHARS FROM STRING                                                                     #
    #                                                                                                                           #
    #############################################################################################################################
    def trimcr(str):
        if debug:
            print('trimcr() '+str)
        if str == '':
            return ''
        if str[-1:] in '\n\r':
            return trimcr(str[:-1])
        else:
            return str

    #############################################################################################################################
    #                                                                                                                           #
    # Display shortened name to fit to 7 characters (e.g., Fruity Chorus = FChorus, EQ Enhancer = EQEnhan)                      #
    #                                                                                                                           #
    #############################################################################################################################


    def DisplayName(name):
        if debug:
            print('DisplayName() ' + name)
        if name == '':
            return ''

        words = name.split()
        if len(words) == 0:
            return ''

        shortName = ''

        for w in words:
            first = True
            for c in w:
                if c.isupper():
                    shortName += c
                elif first:
                    shortName += c
                else:
                    break
                first = False

        lastWord = words[len(words)-1]
        shortName += lastWord[1:]
        if debug:
            print('DisplayName() ' + shortName[0:6])
        return shortName[0:6]

    #############################################################################################################################
    #                                                                                                                           #
    #  CALLED FROM UPDATECOL TO RETURN SLIDER / LEVEL VALUEDS                                                                   #
    #                                                                                                                           #
    #############################################################################################################################
    def AlphaTrack_LevelToSlider(self, Value, Max=midi.FromMIDI_Max):
        return round(Value / Max * self.AlphaTrack_SliderMax)

    #############################################################################################################################
    #                                                                                                                           #
    #  CALLED FROM UPDATECOL TO RETURN SLIDER / LEVEL VALUEDS                                                                   #
    #                                                                                                                           #
    #############################################################################################################################
    def AlphaTrack_SliderToLevel(self, Value, Max=midi.FromMIDI_Max):
        return min(round(Value / self.AlphaTrack_SliderMax * Max), Max)

# --------------------------------------------------------------------------------------------------------------------------------
# EVENTS:
# --------------------------------------------------------------------------------------------------------------------------------
    #############################################################################################################################
    #                                                                                                                           #
    #  Called when the script has been started.                                                                                 #
    #                                                                                                                           #
    #############################################################################################################################
    def OnInit(self):

        self.FirstTrackT[0] = 1
        self.FirstTrack = 0
        self.SmoothSpeed = 469
        self.Clicking = True

        device.setHasMeters()
        self.LastTimeMsg = bytearray(10)

        for m in range(0, len(self.FreeCtrlT)):
            self.FreeCtrlT[m] = 8192  # default free faders to center
        if device.isAssigned():
            device.midiOutSysex(
                bytes([0xF0, 0x00, 0x00, 0x66, 0x14, 0x0C, 1, 0xF7]))
        self.SetBackLight(2)  # backlight timeout to 2 minutes
        self.UpdateClicking()
        self.UpdateMeterMode()
        self.SetPage(self.Page)
        self.SendMsg(chr(32)*112)
        self.SendMsg2(chr(32)*112)
        if debug:
            print('OnInit()')

    #############################################################################################################################
    #                                                                                                                           #
    #  	Called before the script will be stopped.                                                                               #
    #                                                                                                                           #
    #############################################################################################################################
    def OnDeInit(self):

        if device.isAssigned():
            for m in range(0, 8):
                device.midiOutSysex(bytes([0xF0, 0x00, 0x00, 0x66, 0x14, 0x20, m, 0, 0xF7]))
                device.midiOutSysex(bytes(bytearray([0xd1, 0, 0xF7])))
                device.midiOutSysex(bytes(bytearray([0xd1, 16, 0xF7])))
                
            if ui.isClosing():
                # self.SendMsg(chr(32)*112)
                self.SendMsg(
                    "Your QCON Pro X script version is 0.8                   (Please check on www.gadgeteer.home.blog for updates).   ")
                # self.SendMsg2(chr(32)*112)
                self.SendMsg2(ui.getProgTitle() + ' session closed at ' +
                              time.ctime(time.time())+chr(32)*60, 0)
            else:
                self.SendMsg('', 1)

            self.SendAssignmentMsg('   ')
        if debug:
            print('OnDeInit()')

    #############################################################################################################################
    #                                                                                                                           #
    #  	Called on mixer track(s) change, 'index' indicates track index of track that changed or -1 when all tracks changed.     #
    #                                                                                                                           #
    #############################################################################################################################
    def OnDirtyMixerTrack(self, SetTrackNum):
        for m in range(0, len(self.ColT)):
            if (self.ColT[m].TrackNum == SetTrackNum) | (SetTrackNum == -1):
                self.ColT[m].Dirty = True
        if debug:
            print('OnDirtyMixerTrack() '+str(SetTrackNum))

    #############################################################################################################################
    #                                                                                                                           #
    #  Called when something changed that the script might want to respond to.                                                  #
    #                                                                                                                           #
    #############################################################################################################################
    def OnRefresh(self, flags):

        if flags & midi.HW_Dirty_Mixer_Sel:
            self.UpdateMixer_Sel()

        if flags & midi.HW_Dirty_Mixer_Display:
            self.UpdateTextDisplay()
            self.UpdateColT()

        if flags & midi.HW_Dirty_Mixer_Controls:
            for n in range(0, len(self.ColT)):
                if self.ColT[n].Dirty:
                    self.UpdateCol(n)

        # LEDs
        if flags & midi.HW_Dirty_LEDs:
            self.UpdateLEDs()
        if debug:
            print('OnRefresh() '+str(flags))

    #############################################################################################################################
    #                                                                                                                           #
    #   SEND A MESSAGE TO THE SECOND DISPLAY (USSUALLY RAISED BY FL STUDIO)                                                     #
    #                                                                                                                           #
    #############################################################################################################################
    def OnSendTempMsg(self, Msg, Duration=1000):
        if debug:
            print('OnSendTempMsg() '+str(Msg))
        self.SendMsg('  '+Msg.ljust(54, ' '), 0, 2)

    #############################################################################################################################
    #                                                                                                                           #
    #  Called when the beat indicator has changes.                                                                              #
    #                                                                                                                           #
    #############################################################################################################################
    def OnUpdateBeatIndicator(self, Value):

        SyncLEDMsg = [midi.MIDI_NOTEON + (0x5E << 8), midi.MIDI_NOTEON + (
            0x5E << 8) + (0x7F << 16), midi.MIDI_NOTEON + (0x5E << 8) + (0x7F << 16)]

        if device.isAssigned():
            device.midiOutNewMsg(SyncLEDMsg[Value], 128)
        if debug:
            print('OnUpdateBeatIndicator()')

    #############################################################################################################################
    #                                                                                                                           #
    #  Called when peak meters needs to be updated                                                                              #
    #                                                                                                                           #
    #############################################################################################################################
    def OnUpdateMeters(self):
        if self.CurMeterMode == 1:
            if self.Page != MackieCUPage_Free:
                # for m in range(0, len(self.ColT) - 1):
                #    self.ColT[m].Peak = max(self.ColT[m].Peak, round(mixer.getTrackPeaks(self.ColT[m].TrackNum, midi.PEAK_LR_INV) * self.MeterMax))
                for m in range(0, len(self.ColT) - 1):
                    self.ColT[m].Peak = max(0, round(mixer.getTrackPeaks(
                        self.ColT[m].TrackNum, 0) * self.MeterMax))
                n = max(0, round(mixer.getTrackPeaks(MasterPeak, 0) * self.MeterMax))
                device.midiOutSysex(bytes(bytearray([0xd1, n, 0xF7])))
                n = max(0, round(mixer.getTrackPeaks(MasterPeak, 1) * self.MeterMax))
                device.midiOutSysex(bytes(bytearray([0xd1, n+16, 0xF7])))

    #############################################################################################################################
    #                                                                                                                           #
    #  CALLED BY FL WHENEVER IT IS NOT BUSY \\:-)                                                                                     #
    #                                                                                                                           #
    #############################################################################################################################
    def OnIdle(self):
        # ----------------
        # REFRESH METERS
        # ---------------
        if device.isAssigned():
            f = self.Page == MackieCUPage_Free
            for m in range(0,  len(self.ColT) - 1):
                self.ColT[m].Tag = utils.Limited(
                    self.ColT[m].Peak, 0, self.MeterMax)
                self.ColT[m].Peak = 0
                if self.ColT[m].Tag == 0:
                    if self.ColT[m].ZPeak:
                        continue
                    else:
                        self.ColT[m].ZPeak = True
                else:
                    self.ColT[m].ZPeak = f
                device.midiOutMsg(midi.MIDI_CHANAFTERTOUCH +
                                  (self.ColT[m].Tag << 8) + (m << 12))
        # -------------------------
        # UPDATE THE TIME DISPLAY
        # -------------------------
        if ui.getTimeDispMin():
            # HHH.MM.SS.CC_
            if playlist.getVisTimeBar() == -midi.MaxInt:
                s = '-   0'
            else:
                n = abs(playlist.getVisTimeBar())
                h, m = utils.DivModU(n, 60)
                # todo sign of...
                s = utils.Zeros_Strict(
                    (h * 100 + m) * utils.SignOf(playlist.getVisTimeBar()), 5, ' ')

            s = s + utils.Zeros_Strict(abs(playlist.getVisTimeStep()), 2) + \
                utils.Zeros_Strict(playlist.getVisTimeTick(), 2) + ' '
        else:
            # BBB.BB.__.TTT
            s = utils.Zeros_Strict(playlist.getVisTimeBar(), 3, ' ') + utils.Zeros_Strict(abs(
                playlist.getVisTimeStep()), 2) + '  ' + utils.Zeros_Strict(playlist.getVisTimeTick(), 3)

        self.SendTimeMsg(s)
        # -------------------------------
        # MANAGE ANY TEMPORARY MESSAGES
        # -------------------------------
        if self.TempMsgDirty:
            self.UpdateTempMsg()
            self.TempMsgDirty = False

        if (self.TempMsgCount > 0) & (self.SliderHoldCount <= 0) & (not ui.isInPopupMenu()):
            self.TempMsgCount -= 1
            if self.TempMsgCount == 0:
                self.UpdateTempMsg()

    #############################################################################################################################
    #                                                                                                                           #
    #  Called for all MIDI messages that were not handled by OnMidiIn.       .                                                  #
    #                                                                                                                           #
    #############################################################################################################################
    def OnMidiMsg(self, event):

        ArrowStepT = [2, -2, -1, 1]
        CutCopyMsgT = ('Cut', 'Copy', 'Paste', 'Insert',
                       'Delete')  # FPT_Cut..FPT_Delete
        if debug:
            print("midiID,HEX,data1,hex,data2,hex")
            print(event.midiId, hex(event.midiId), event.data1,
                  hex(event.data1), event.data2, hex(event.data2))

        #############################################################################################################################
        #                                                                                                                           #
        #   CONTROL CHANGE                                                                                                     #
        #                                                                                                                           #
        #############################################################################################################################
        if (event.midiId == midi.MIDI_CONTROLCHANGE):
            if debug:
                print("midi control change")
            if self.DefaultJogToPlaylist:
                ui.setFocused(midi.widPlaylist)
            if (event.midiChan == 0):
                event.inEv = event.data2
                if event.inEv >= 0x40:
                    event.outEv = -(event.inEv - 0x40)
                else:
                    event.outEv = event.inEv
                if event.data1 == 0x3C:
                    self.Jog(event)
                    event.handled = True

                # knobs
                elif event.data1 in [0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17]:
                    r = utils.KnobAccelToRes2(event.outEv)  # todo outev signof
                    Res = r * (1 / (40 * 2.5))
                    if self.Page == MackieCUPage_FX:
                        self.SetKnobValue(event.data1 - 0x10, event.outEv, Res)
                        event.handled = True
                    if self.Page == MackieCUPage_Free:
                        i = event.data1 - 0x10
                        self.ColT[i].Peak = self.ActivityMax
                        event.data1 = self.ColT[i].BaseEventID + \
                            int(self.ColT[i].KnobHeld)
                        event.isIncrement = 1
                        s = chr(0x7E + int(event.outEv < 0))
                        self.SendMsg2(
                            'Free knob ' + str(event.data1) + ': ' + s)
                        device.processMIDICC(event)
                        device.hardwareRefreshMixerTrack(self.ColT[i].TrackNum)
                    else:
                        self.SetKnobValue(event.data1 - 0x10, event.outEv, Res)
                        event.handled = True
                else:
                    event.handled = False  # for extra CCs in emulators
            else:
                event.handled = False  # for extra CCs in emulators

        #############################################################################################################################
        #                                                                                                                           #
        #   PITCH BEND (FADERS)                                                                                                     #
        #                                                                                                                           #
        #############################################################################################################################
        elif event.midiId == midi.MIDI_PITCHBEND:
            if debug:
                print("Midi pitchbend")
            if event.midiChan <= 8:
                event.inEv = event.data1 + (event.data2 << 7)
                event.outEv = (event.inEv << 16) // 16383
                event.inEv -= 0x2000

                if self.Page == MackieCUPage_Free:
                    self.ColT[event.midiChan].Peak = self.ActivityMax
                    self.FreeCtrlT[self.ColT[event.midiChan].TrackNum] = event.data1 + \
                        (event.data2 << 7)
                    device.hardwareRefreshMixerTrack(
                        self.ColT[event.midiChan].TrackNum)
                    event.data1 = self.ColT[event.midiChan].BaseEventID + 7
                    event.midiChan = 0
                    event.midiChanEx = event.midiChanEx & (not 0xF)
                    self.SendMsg2('Free slider ' + str(event.data1) + ': ' +
                                  ui.getHintValue(event.outEv, midi.FromMIDI_Max))
                    device.processMIDICC(event)
                elif self.ColT[event.midiChan].SliderEventID >= 0:
                    # slider (mixer track volume)
                    if self.ColT[event.midiChan].TrackNum >= 0:
                        if (self.Page != MackieCUPage_EQ) and (self.Page != MackieCUPage_FX):
                            if mixer.trackNumber != self.ColT[event.midiChan].TrackNum:
                                mixer.setTrackNumber(
                                    self.ColT[event.midiChan].TrackNum)
                    event.handled = True
                    mixer.automateEvent(self.ColT[event.midiChan].SliderEventID, self.AlphaTrack_SliderToLevel(
                        event.inEv + 0x2000), midi.REC_MIDIController, self.SmoothSpeed)
                    # hint
                    n = mixer.getAutoSmoothEventValue(
                        self.ColT[event.midiChan].SliderEventID)
                    s = mixer.getEventIDValueString(
                        self.ColT[event.midiChan].SliderEventID, n)
                    if s != '':
                        s = ': ' + s
                    self.SendMsg2(self.ColT[event.midiChan].SliderName + s)

        #############################################################################################################################
        #                                                                                                                           #
        #   MIDI NOTEON/OFF                                                                                                         #
        #                                                                                                                           #
        #############################################################################################################################
        elif (event.midiId == midi.MIDI_NOTEON) | (event.midiId == midi.MIDI_NOTEOFF):  # NOTE
            if debug:
                print("midi note on or off")

            if event.midiId == midi.MIDI_NOTEON:
                if event.data2 > 0:
                    if event.data1 in [0x68, 0x69, 0x70]:
                        self.SliderHoldCount += -1 + (int(event.data2 > 0) * 2)

                    # -------
                    # MIXER
                    # -------
                    elif event.data1 == 0x3F:  # Mixer
                        if self.Shift:
                            if self.ShowTrackNumbers:
                                self.ShowTrackNumbers = False
                            else:
                                self.ShowTrackNumbers = True
                            self.UpdateTextDisplay()
                        else:
                            ui.showWindow(midi.widMixer)
                            ui.setFocused(midi.widMixer)
                            self.SendMsg2("The Mixer Window is Open")
                    # ---------
                    # CHANNEL
                    # --------
                    elif event.data1 == 0x40:  # Channel Rack
                        if self.Shift:
                            if ui.getFocused(5) == 0:
                                channels.focusEditor(channels.getChannelIndex(channels.selectedChannel()))
                                channels.showCSForm(channels.getChannelIndex(channels.selectedChannel(-1)))
                            else:
                                channels.focusEditor(channels.getChannelIndex(channels.selectedChannel()))
                                channels.showCSForm(channels.getChannelIndex(channels.selectedChannel(-1)), 0)
                        else:
                            ui.showWindow(midi.widChannelRack)
                            ui.setFocused(midi.widChannelRack)
                            self.SendMsg2("The Channel Rack Window is Open")
                    # -------
                    # TEMPO
                    # -------
                    elif event.data1 == 0x41:
                        transport.globalTransport(midi.FPT_TapTempo, 1)
                        s = str(mixer.getCurrentTempo(True))[:-2]
                        self.SendMsg2("Tempo: "+s)
                    # --------
                    # WINDOW 
                    # --------
                    elif event.data1 == 0x4c:
                        ui.nextWindow()
                        s = ui.getFocusedFormCaption()
                        if s != "":
                            self.SendMsg2('Current window: ' + s)


                if (event.pmeFlags & midi.PME_System != 0):
                    # F1..F8
                    if self.Shift & (event.data1 in [0x36, 0x37, 0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D]):
                        transport.globalTransport(midi.FPT_F1 - 0x36 +
                                                  event.data1, int(event.data2 > 0) * 2, event.pmeFlags)
                        event.data1 = 0xFF

                    if self.Control & (event.data1 in [0x36, 0x37, 0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D]):
                        ui.showWindow(midi.widPlaylist)
                        ui.setFocused(midi.widPlaylist)
                        transport.globalTransport(midi.FPT_Menu, int(
                            event.data2 > 0) * 2, event.pmeFlags)
                        time.sleep(0.1)
                        f = int(1 + event.data1 - 0x36)
                        for x in range(0, f):
                            transport.globalTransport(midi.FPT_Down, int(
                                event.data2 > 0) * 2, event.pmeFlags)
                            time.sleep(0.01)
                        time.sleep(0.1)
                        transport.globalTransport(midi.FPT_Enter, int(
                            event.data2 > 0) * 2, event.pmeFlags)
                        event.data1 = 0xFF

                    #---------------
                    # MODE (METERS)
                    #---------------
                    if event.data1 == 0x34:
                        if event.data2 > 0:
                            if self.Shift:
                                self.ExtenderPos = abs(self.ExtenderPos - 1)
                                self.FirstTrackT[self.FirstTrack] = 1
                                self.SetPage(self.Page)
                                self.SendMsg2(
                                    'Extender on ' + self.MackieCU_ExtenderPosT[self.ExtenderPos], 1500)
                            else:
                                self.MeterMode = (self.MeterMode + 1) % 2
                                self.SendMsg2(
                                    self.MackieCU_MeterModeNameT[self.MeterMode])
                                self.UpdateMeterMode()
                                device.dispatch(0, midi.MIDI_NOTEON +
                                                (event.data1 << 8) + (event.data2 << 16))
                                device.midiOutSysex(
                                    bytes(bytearray([0xd1, 0, 0xF7])))
                                device.midiOutSysex(
                                    bytes(bytearray([0xd1, 16, 0xF7])))
                    #-------------                
                    # TIME FORMAT
                    #-------------
                    elif event.data1 == 0x35:
                        if event.data2 > 0:
                            ui.setTimeDispMin()
                            if ui.getTimeDispMin():
                                SendMsg2("Time display set to M:S:CS (Time)")
                            else:
                                SendMsg2("Time display set to B:S:T (Beats)")
                    # --------------
                    # SCRUB BUTTON
                    # --------------
                    elif event.data1 == 0x65:  # self.Scrub
                        if event.data2 > 0:
                            self.Scrub = not self.Scrub
                            self.UpdateLEDs()

                    # --------------
                    # JOG SOURCES
                    # --------------
                    #elif event.data1 in [0x3E, 0x3F, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x48, 0x55, 0x64, 0x46, 0x4C]: (X-Touch specific?)
                    elif event.data1 in [0x3E, 0x3F, 0x40, 0x41, 0x48, 0x64, 0x46, 0x4C]:
                        # update jog source
                        self.SliderHoldCount += -1 + (int(event.data2 > 0) * 2)
                        if event.data1 in [0x64, 0x4C]:
                            device.directFeedback(event)
                        if event.data2 == 0:
                            if self.JogSource == event.data1:
                                self.SetJogSource(0)
                        else:
                            self.SetJogSource(event.data1)
                            if event.data1 ==0x48: #markers
                                ui.showWindow(midi.widPlaylist)
                                ui.setFocused(midi.widPlaylist)
                            event.outEv = 0
                            self.Jog(event)  # for visual feedback

                    # ---------------
                    # ARROW BUTTONS
                    # ---------------
                    elif event.data1 in [0x60, 0x61, 0x62, 0x63]:
                        if self.JogSource == 0x64:
                            if event.data1 == 0x60:
                                transport.globalTransport(
                                    midi.FPT_VZoomJog + int(self.Shift), -1, event.pmeFlags)
                            elif event.data1 == 0x61:
                                transport.globalTransport(
                                    midi.FPT_VZoomJog + int(self.Shift), 1, event.pmeFlags)
                            elif event.data1 == 0x62:
                                transport.globalTransport(
                                    midi.FPT_HZoomJog + int(self.Shift), -1, event.pmeFlags)
                            elif event.data1 == 0x63:
                                transport.globalTransport(
                                    midi.FPT_HZoomJog + int(self.Shift), 1, event.pmeFlags)

                        elif self.JogSource == 0:
                            transport.globalTransport(
                                midi.FPT_Up - 0x60 + event.data1, int(event.data2 > 0) * 2, event.pmeFlags)
                        else:
                            if event.data2 > 0:
                                event.inEv = ArrowStepT[event.data1 -
                                                        0x60]
                                event.outEv = event.inEv
                                self.Jog(event)
                    #------------
                    # COUNTDOWN:
                    #------------
                    elif event.data1 == 0x58:
                        if event.data2 == 0:
                            transport.globalTransport(midi.FPT_CountDown, 1)
                            if ui.isPrecountEnabled():
                                SendMsg2("Count in enabled for recording")
                            else:
                                SendMsg2("Count in disabled for recording")
                    #----------------            
                    # PATTERN / SONG
                    #----------------
                    elif event.data1 == 0x5a:
                        if event.data2 > 0:
                            transport.globalTransport(midi.FPT_Loop, 1)
                            Looper = transport.getLoopMode()
                            if (Looper == midi.SM_Pat):
                                self.SendMsg2("Pattern Mode")
                            else:
                                self.SendMsg2("Song Mode")
                    #-------------------
                    # CONTROL SMOOTHING
                    #-------------------
                    elif event.data1 == 0x33:
                        if event.data2 > 0:
                            self.SmoothSpeed = int(self.SmoothSpeed == 0) * 469
                            self.UpdateLEDs()
                            self.SendMsg2('Control smoothing ' +
                                          OffOnStr[int(self.SmoothSpeed > 0)])

                    # ------------------------------
                    # CUT/COPY/PASTE/INSERT/DELETE
                    # ------------------------------
                    elif event.data1 in [0x36, 0x37, 0x38, 0x39, 0x3A]:
                        transport.globalTransport(midi.FPT_Cut + event.data1 -
                                                  0x36, int(event.data2 > 0) * 2, event.pmeFlags)
                        if event.data2 > 0:
                            self.SendMsg2(
                                CutCopyMsgT[midi.FPT_Cut + event.data1 - 0x36 - 50])
                    # -------------------
                    # TOGGLE UNDO / REDO
                    # -------------------
                    elif event.data1 in [0x3C,0x3d]:
                        if (transport.globalTransport(midi.FPT_Undo, int(event.data2 > 0) * 2, event.pmeFlags) == midi.GT_Global) & (event.data2 > 0):
                            self.OnSendTempMsg(
                                ui.getHintMsg() + ' (level ' + general.getUndoLevelHint() + ')')


                    # --------
                    # PATTERN
                    # --------
                        elif event.data1 == 0x3E:
                            if event.data2 > 0:
                                #if self.Shift:
                                #    #open the piano roll:
                                #    ui.hideWindow(midi.widPlaylist)
                                #    ui.showWindow(midi.widPianoRoll)
                                #    ui.setFocused(midi.widPianoRoll)
                                #else:    
                                if ui.getVisible(midi.widPlaylist):
                                    ui.hideWindow(midi.widPlaylist)
                                else:
                                    ui.showWindow(midi.widPlaylist)
                                    ui.setFocused(midi.widPlaylist)
                                    sel = -1
                                    for p in range(0, patterns.patternCount()-1):
                                        if patterns.isPatternSelected(p):
                                            sel = p
                                            break
                                    if sel == -1:
                                        SendMsg2("Playlist Opened (use jog dial to navigate patterns)")

                                    else:
                                        SendMsg2("Pattern Selected:"+patterns.getPatternName(p)+" (use jog dial to navigate)")
                                        patterns.selectPattern(p)
                                # Ensure that we are in Pattern Mode:
                                if transport.getLoopMode()==1:   
                                    transport.globalTransport(midi.FPT_Loop, int(event.data2 > 0) * 2, event.pmeFlags)     



                    # ---------------------------
                    # FREE1 - UNMUTE ALL TRACKS
                    # ---------------------------
                    elif event.data1 == 0x42:
                        if event.data2 > 0:
                            if self.Shift:
                                for m in range(0,  mixer.trackCount()):
                                    if mixer.isTrackArmed(m):
                                        mixer.armTrack(m)
                                self.SendMsg2("All tracks disarmed")
                            else:
                                for m in range(0,  mixer.trackCount()):
                                    if mixer.isTrackMuted(m):
                                        mixer.muteTrack(m)
                                self.SendMsg2("All tracks unmuted")

                    # -----------------------------------------------------------
                    # FREE2 - SELECT FIRST TRACK ON MIXER BANKING (DEFAULT OFF)
                    # -----------------------------------------------------------
                    elif event.data1 == 0x43:
                        if event.data2 > 0:
                            if self.MixerScroll:
                                self.MixerScroll = False
                                self.SendMsg2(
                                    "Banking functionality reset to default")
                            else:
                                self.MixerScroll = True
                                self.SendMsg2(
                                    "Banking always selects and shows first track in the bank")

                    # -----------------------------------------------
                    # FREE3 - JOG DIAL ALWAYS CONTROLS THE PLAYLIST
                    # -----------------------------------------------
                    elif event.data1 == 0x44 and event.data2 > 0:  # shift f7 *****
                        if event.data2 > 0:
                            if self.DefaultJogToPlaylist:
                                self.DefaultJogToPlaylist = False
                                self.SendMsg2(
                                    "Jog Dial functionality reset to default")
                            else:
                                self.DefaultJogToPlaylist = True
                                self.SendMsg2(
                                    "Jog Dial always controls the playlist")

                    # ----------------------------------------------
                    # FREE4 - DEFAULTING BANKING COLOURS FOR MIXER
                    # ---------------------------------------------

                    # Could add more options here?
                    # Would be good to be able to invoke the new colour picker?
                    elif event.data1 == 0x45:
                        if event.data2 > 0:
                            #Activate the mixer so we can see what is happening:
                            ui.showWindow(midi.widMixer)
                            ui.setFocused(midi.widMixer)
                            s="Defaulted"
                            if self.Shift:
                                for m in range(0,  mixer.trackCount()): mixer.setTrackColor(m, -10261391)
                            else:
                                if self.colourOptions == 0:
                                    s="Banking Optimised (with gradient fills)"
                                    self.colourOptions = 1
                                    for m in range(0,  mixer.trackCount()):
                                        mixer.setTrackColor(m, TrackColours[m])
                                        #self.setLinkedChannelColour(m,TrackColours[m])
                                else:
                                    self.colourOptions = 0
                                    s="Banking Optimised (with solid colours)"
                                    splitter = 0
                                    color = BankingColours[splitter]
                                    for m in range(0,  mixer.trackCount()):
                                        mixer.setTrackColor(m, color)
                                        if math.remainder(m, 8) == 0:
                                            splitter = splitter+1
                                            if splitter == 12:
                                                splitter = 0
                                            color = BankingColours[splitter]
                            self.SendMsg2("Mixer colours:"+s)                

                    # ---------
                    # BROWSER
                    # ---------
                    elif event.data1 == 0x4a:
                        ui.showWindow(midi.widBrowser)
                        # ui.setFocused(midi.widBrowser)
                        self.SendMsg2("Browser Window Open")

                    # ------
                    # MAIN
                    # ------
                    elif event.data1 == 0x4b:
                        if event.data2 > 0:
                                transport.globalTransport(midi.FPT_F11, 1) # Main song Window
                                self.SendMsg2("Main Window Open")
                                #ui.showWindow(midi.widChannelRack)
                                #ui.setFocused(midi.widChannelRack)

                    # ---------------------------
                    # BANK UP / DOWN (8 tracks)
                    # ---------------------------
                    elif (event.data1 == 0x2E) | (event.data1 == 0x2F):  # mixer bank
                        if event.data2 > 0:
                            self.SetFirstTrack(
                                self.FirstTrackT[self.FirstTrack] - 8 + int(event.data1 == 0x2F) * 16)
                            device.dispatch(0, midi.MIDI_NOTEON +
                                            (event.data1 << 8) + (event.data2 << 16))
                            if self.MixerScroll:
                                if self.ColT[event.midiChan].TrackNum >= 0:
                                    if mixer.trackNumber != self.ColT[event.midiChan].TrackNum:
                                        mixer.setTrackNumber(
                                            self.ColT[event.midiChan].TrackNum, midi.curfxScrollToMakeVisible | midi.curfxMinimalLatencyUpdate)

                            if (self.CurPluginID != -1):  # Selected Plugin
                                if (event.data1 == 0x2E) & (self.PluginParamOffset >= 8):
                                    self.PluginParamOffset -= 8
                                elif (event.data1 == 0x2F) & (self.PluginParamOffset + 8 < plugins.getParamCount(mixer.trackNumber(), self.CurPluginID + self.CurPluginOffset) - 8):
                                    self.PluginParamOffset += 8
                            else:  # No Selected Plugin
                                if (event.data1 == 0x2E) & (self.CurPluginOffset >= 2):
                                    self.CurPluginOffset -= 2
                                elif (event.data1 == 0x2F) & (self.CurPluginOffset < 2):
                                    self.CurPluginOffset += 2

                    # ---------------------------
                    # MOVE UP / DOWN (1 track)
                    # ---------------------------
                    elif (event.data1 == 0x30) | (event.data1 == 0x31):
                        if event.data2 > 0:
                            self.SetFirstTrack(
                                self.FirstTrackT[self.FirstTrack] - 1 + int(event.data1 == 0x31) * 2)
                            device.dispatch(
                                0, midi.MIDI_NOTEON + (event.data1 << 8) + (event.data2 << 16))

                    # ---------------------
                    # FLIP FADERS & VPOTS
                    # ---------------------
                    elif event.data1 == 0x32:  # self.Flip
                        if event.data2 > 0:
                            self.Flip = not self.Flip
                            device.dispatch(0, midi.MIDI_NOTEON +
                                            (event.data1 << 8) + (event.data2 << 16))
                            self.UpdateColT()
                            self.UpdateLEDs()


                    elif event.data1 in [0x28,  0x2A, 0x29, 0x2B, 0x2C, 0x2D]:  # self.Page
                        self.SliderHoldCount += -1 + (int(event.data2 > 0) * 2)
                        if event.data2 > 0:
                            n = event.data1 - 0x28
                            # print(event.data1)
                            if event.data1 == 0x2B:
                                self.SendMsg2(
                                    'FX for track "'+mixer.getTrackName(mixer.trackNumber())+self.MackieCU_PageNameT[n])
                            elif event.data1 == 0x2C:
                                self.SendMsg2(
                                    'EQ for track "'+mixer.getTrackName(mixer.trackNumber())+self.MackieCU_PageNameT[n])
                            elif event.data1 == 42:
                                self.SendMsg2(
                                    'Sends for track "'+mixer.getTrackName(mixer.trackNumber())+self.MackieCU_PageNameT[n])
                            else:
                                self.SendMsg2(self.MackieCU_PageNameT[n])
                            self.SetPage(n)
                            device.dispatch(0, midi.MIDI_NOTEON +
                                            (event.data1 << 8) + (event.data2 << 16))

                    elif event.data1 == 0x54:  # self.Shift
                        self.Shift = event.data2 > 0
                        device.directFeedback(event)

                    #elif event.data1 == 0x47:  # self.Option
                    #    self.Option = event.data2 > 0
                    #    device.directFeedback(event)
                    #elif event.data1 == 0x49:  # self.Alt
                    #    self.Alt = event.data2 > 0
                    #    device.directFeedback(event)

                    # ------
                    # MENU
                    # ------
                    elif event.data1 == 0x51:  # menu (was self.Control)
                        #    self.Control = event.data2 > 0
                        #    device.directFeedback(event)
                        self.SendMsg2("Use the arrow & enter keys to navigate the menu")
                        transport.globalTransport(midi.FPT_Menu, int(
                            event.data2 > 0) * 2, event.pmeFlags)
                            
                    # --------
                    # EDISON
                    # --------
                    elif event.data1 ==0x55: # -1:  # open audio editor in current mixer track
                        if event.data2 > 0:
                            ui.launchAudioEditor(False, '', mixer.trackNumber(),
                                                 'AudioLoggerTrack.fst', '')
                            self.SendMsg2('Audio editor ready for track '+mixer.getTrackName(mixer.trackNumber()))


                    # -----------
                    # METRONOME
                    # -----------
                    elif event.data1 == 0x59:  # metronome/button self.Clicking
                        if event.data2 > 0:
                            if self.Shift:
                                self.Clicking = not self.Clicking
                                self.UpdateClicking()
                                self.SendMsg2('Metronome self clicking is ' + OffOnStr[self.Clicking])
                            else:
                                transport.globalTransport(
                                    midi.FPT_Metronome, 1, event.pmeFlags)
                                # if (ui.isMetronomeEnabled):
                                #    self.SendMsg2("Metronome is Enabled")
                                # else:
                                #    self.SendMsg2("Metronome is Disabled")

                    elif event.data1 == -1:  # precount
                        if event.data2 > 0:
                            transport.globalTransport(
                                midi.FPT_CountDown, 1, event.pmeFlags)

                    # ---------
                    # << & >>
                    # ---------
                    elif (event.data1 == 0x5B) | (event.data1 == 0x5C):
                        if self.Shift:
                            if event.data2 == 0:
                                v2 = 1
                            elif event.data1 == 0x5B:
                                v2 = 0.5
                            else:
                                v2 = 2
                            transport.setPlaybackSpeed(v2)
                        else:
                            transport.globalTransport(midi.FPT_Rewind + int(event.data1 ==
                                                                            0x5C), int(event.data2 > 0) * 2, event.pmeFlags)
                        device.directFeedback(event)

                    # ------
                    # STOP
                    # ------
                    elif event.data1 == 0x5D:
                        transport.globalTransport(midi.FPT_Stop, int(
                            event.data2 > 0) * 2, event.pmeFlags)

                    # ------
                    # PLAY
                    # ------
                    elif event.data1 == 0x5E:
                        transport.globalTransport(midi.FPT_Play, int(
                            event.data2 > 0) * 2, event.pmeFlags)
                    # --------
                    # RECORD
                    # --------
                    elif event.data1 == 0x5F:  # record
                        transport.globalTransport(midi.FPT_Record, int(
                            event.data2 > 0) * 2, event.pmeFlags)


                    # -------------
                    # SONG / LOOP
                    # -------------
                    elif event.data1 == 0x5A:  # song/loop
                        transport.globalTransport(midi.FPT_Loop, int(event.data2 > 0) * 2, event.pmeFlags)
                    # ------
                    # SNAP
                    # ------
                    elif event.data1 == 0x4E:
                        if self.Shift:
                            if event.data2 > 0:
                                transport.globalTransport(
                                    midi.FPT_SnapMode, 1, event.pmeFlags)
                            else:
                                transport.globalTransport(midi.FPT_Snap, int(
                                    event.data2 > 0) * 2, event.pmeFlags)

                    # --------
                    # ESCAPE
                    # --------
                    elif event.data1 == 0x52:
                        if (self.Shift == False):
                            transport.globalTransport(
                                midi.FPT_Escape + int(self.Shift) * 2, int(event.data2 > 0) * 2, event.pmeFlags)
                    # --------
                    # ENTER
                    # --------
                    elif event.data1 == 0x53:
                        transport.globalTransport(
                            midi.FPT_Enter + int(self.Shift) * 2, int(event.data2 > 0) * 2, event.pmeFlags)

                    # ------------
                    # VPOT PUSH
                    # ------------
                    elif event.data1 in [0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27]:
                        if self.Page == MackieCUPage_Free:
                            i = event.data1 - 0x20
                            self.ColT[i].KnobHeld = event.data2 > 0
                            if event.data2 > 0:
                                self.ColT[i].Peak = self.ActivityMax
                                event.data1 = self.ColT[i].BaseEventID + 2
                                event.outEv = 0
                                event.isIncrement = 2
                                self.SendMsg2(
                                    'Free knob switch ' + str(event.data1))
                                device.processMIDICC(event)
                            device.hardwareRefreshMixerTrack(
                                self.ColT[i].TrackNum)
                            return
                        elif event.data2 > 0:
                            n = event.data1 - 0x20
                            if self.Page == MackieCUPage_Sends:
                                if mixer.setRouteTo(mixer.trackNumber(), self.ColT[n].TrackNum, -1) < 0:
                                    self.SendMsg2('Cannot send to this track')
                                else:
                                    if mixer.getRouteSendActive(mixer.trackNumber(), self.ColT[n].TrackNum):
                                        self.SendMsg2("VPOT set for send to " + mixer.getTrackName(self.ColT[n].TrackNum))
                                    else:
                                        self.SendMsg2("The "+mixer.getTrackName(self.ColT[n].TrackNum)+" VPOT has been reset")
                                    mixer.afterRoutingChanged()
                            else:
                                if self.Page == MackieCUPage_EQ:
                                    if event.data1 == 0x27: # "Reset All"
                                        self.SetKnobValue(0, midi.MaxInt)
                                        self.SetKnobValue(1, midi.MaxInt)
                                        self.SetKnobValue(2, midi.MaxInt)
                                        self.SetKnobValue(3, midi.MaxInt)
                                        self.SetKnobValue(4, midi.MaxInt)
                                        self.SetKnobValue(5, midi.MaxInt)
                                        self.SetKnobValue(6, midi.MaxInt)
                                        self.SetKnobValue(7, midi.MaxInt)
                                        SendMsg2("All EQ levels reset")
                                else:
                                    self.SetKnobValue(n, midi.MaxInt)
                                    if self.Page == MackieCUPage_FX:
                                            SendMsg2("\\ Pending Functionality! \\")
                    # -------------------
                    # FREE HOLD BUTTONS
                    # -------------------
                    elif (event.data1 >= 0) & (event.data1 <= 0x1F):
                        if self.Page == MackieCUPage_Free:
                            i = event.data1 % 8
                            self.ColT[i].Peak = self.ActivityMax
                            event.data1 = self.ColT[i].BaseEventID + \
                                3 + event.data1 // 8
                            event.inEv = event.data2
                            event.outEv = int(event.inEv > 0) * \
                                midi.FromMIDI_Max
                            self.SendMsg2('Free button ' + str(event.data1) +
                                          ': ' + OffOnStr[event.outEv > 0])
                            device.processMIDICC(event)
                            device.hardwareRefreshMixerTrack(self.ColT[i].TrackNum)
                            return


                if (event.pmeFlags & midi.PME_System_Safe != 0):
                    # shift options with f1 ..f8
                    # F1..F8
                    #if self.Shift & (event.data1 in [0x36, 0x37, 0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D]):
                    #    transport.globalTransport(midi.FPT_F1 - 0x36 +
                    #                              event.data1, int(event.data2 > 0) * 2, event.pmeFlags)
                    #     event.data1 = 0xFF
                    # -----------------------------------------------
                    # LINK SELECTED CHANNELS TO CURRENT MIXER TRACK
                    # -----------------------------------------------
                    if event.data1 == 0x47:
                        if event.data2 > 0:
                            if self.Shift:
                                mixer.linkTrackToChannel(
                                    midi.ROUTE_StartingFromThis)
                            else:
                                mixer.linkTrackToChannel(midi.ROUTE_ToThis)
                                self.SendMsg2(
                                    "Chanel Track and Mixer Track now linked")
                    # -----------
                    # ITEM MENU
                    # -----------
                    elif event.data1 == 0x3B:
                        transport.globalTransport(midi.FPT_ItemMenu, int(
                            event.data2 > 0) * 2, event.pmeFlags)
                        if event.data2 > 0:
                            self.SendMsg2('Item Menu', 10)

 
                    # -------------------
                    # IN / OUT / SELECT
                    # -------------------
                    elif event.data1 in [0x4D, 0x4E, 0x4F]:
                        #Ensure the playlist is selected:
                        ui.showWindow(midi.widPlaylist)
                        ui.setFocused(midi.widPlaylist)
                        if event.data1 == 0x4F:
                            n = midi.FPT_Punch
                        else:
                            n = midi.FPT_PunchIn + event.data1 - 0x4D
                        if event.data1 >= 0x4E:
                            self.SliderHoldCount += -1 + \
                                (int(event.data2 > 0) * 2)
                        if not ((event.data1 == 0x4D) & (event.data2 == 0)):
                            device.directFeedback(event)
                        if (event.data1 >= 0x4E) & (event.data2 >= int(event.data1 == 0x4E)):
                            if device.isAssigned():
                                device.midiOutMsg(
                                    (0x4D << 8) + midi.TranzPort_OffOnT[False])
                        if transport.globalTransport(n, int(event.data2 > 0) * 2, event.pmeFlags) == midi.GT_Global:
                            t = -1
                            if n == midi.FPT_Punch:
                                if event.data2 != 1:
                                    t = int(event.data2 != 2)
                            elif event.data2 > 0:
                                t = int(n == midi.FPT_PunchOut)
                            if t >= 0:
                                self.SendMsg2(ui.getHintMsg())


                    # -----------
                    # ADD MARKER
                    # -----------
                    elif (event.data1 == 0x49): 
                        if (transport.globalTransport(midi.FPT_AddMarker + int(self.Shift), int(event.data2 > 0) * 2, event.pmeFlags) == midi.GT_Global) & (event.data2 > 0):
                            self.SendMsg2(ui.getHintMsg())

                    # --------
                    # SELECT
                    # --------
                    elif (event.data1 >= 0x18) & (event.data1 <= 0x1F):
                        if event.data2 > 0:
                            i = event.data1 - 0x18

                            ui.showWindow(midi.widMixer)
                            ui.setFocused(midi.widMixer)
                            self.UpdateLEDs()
                            mixer.setTrackNumber(
                                self.ColT[i].TrackNum, midi.curfxScrollToMakeVisible | midi.curfxMinimalLatencyUpdate)

                            if self.Control:  # Link channel to track
                                mixer.linkTrackToChannel(midi.ROUTE_ToThis)
                            # Show Full Trackname on second display:
                            # EXPAND WITH CONTEXT?
                            SendMsg2(mixer.getTrackName(self.ColT[i].TrackNum))
                    # ------
                    # SOLO
                    # ------
                    elif (event.data1 >= 0x8) & (event.data1 <= 0xF):  # solo
                        if event.data2 > 0:
                            i = event.data1 - 0x8
                            self.ColT[i].solomode = midi.fxSoloModeWithDestTracks
                            if self.Shift:
                                Include(self.ColT[i].solomode,
                                        midi.fxSoloModeWithSourceTracks)
                            mixer.soloTrack(self.ColT[i].TrackNum,
                                            midi.fxSoloToggle, self.ColT[i].solomode)
                            mixer.setTrackNumber(
                                self.ColT[i].TrackNum, midi.curfxScrollToMakeVisible)

                    # ------
                    # MUTE
                    # ------
                    elif (event.data1 >= 0x10) & (event.data1 <= 0x17):  # mute
                        if event.data2 > 0:
                            mixer.enableTrack(
                                self.ColT[event.data1 - 0x10].TrackNum)

                    elif (event.data1 >= 0x0) & (event.data1 <= 0x7):  # arm
                        if event.data2 > 0:
                            mixer.armTrack(self.ColT[event.data1].TrackNum)
                            if mixer.isTrackArmed(self.ColT[event.data1].TrackNum):
                                self.SendMsg2(mixer.getTrackName(
                                    self.ColT[event.data1].TrackNum) + ' recording to ' + mixer.getTrackRecordingFileName(self.ColT[event.data1].TrackNum), 2500)
                            else:
                                self.SendMsg2(mixer.getTrackName(
                                    self.ColT[event.data1].TrackNum) + ' unarmed')
                    # ------
                    # SAVE
                    # ------
                    elif event.data1 == 0x50:  # save/save new
                        transport.globalTransport(
                            midi.FPT_Save + int(self.Shift), int(event.data2 > 0) * 2, event.pmeFlags)
                    event.handled = True
                else:
                    event.handled = False
            else:
                event.handled = False
        if debug:
            print('OnMidiMsg() '+str(event))

    #############################################################################################################################
    #                                                                                                                           #
    #  HANDLES KNOB FUNCTIONS                                                                                                   #
    #                                                                                                                           #
    #############################################################################################################################

    def SetKnobValue(self, Num, Value, Res=midi.EKRes):
        if (self.ColT[Num].KnobEventID >= 0) & (self.ColT[Num].KnobMode < 4):
            if Value == midi.MaxInt:
                if self.Page == MackieCUPage_FX:
                    if self.ColT[Num].KnobPressEventID >= 0:
                        Value = channels.incEventValue(
                            self.ColT[Num].KnobPressEventID, 0, midi.EKRes)
                        channels.processRECEvent(
                            self.ColT[Num].KnobPressEventID, Value, midi.REC_Controller)
                        s = mixer.getEventIDName(
                            self.ColT[Num].KnobPressEventID)
                        self.SendMsg2(s)
                    self.CurPluginID = Num
                    self.PluginParamOffset = 0
                    self.UpdateColT()
                    self.UpdateLEDs()
                    self.UpdateTextDisplay()
                    return
                else:
                    mixer.automateEvent(
                        self.ColT[Num].KnobResetEventID, self.ColT[Num].KnobResetValue, midi.REC_MIDIController, self.SmoothSpeed)
            else:
                mixer.automateEvent(
                    self.ColT[Num].KnobEventID, Value, midi.REC_Controller, self.SmoothSpeed, 1, Res)
            # hint
            n = mixer.getAutoSmoothEventValue(self.ColT[Num].KnobEventID)
            s = mixer.getEventIDValueString(self.ColT[Num].KnobEventID, n)
            if s != '':
                s = ': ' + s
            self.SendMsg2(self.ColT[Num].KnobName + s)
        if debug:
            print('SetKnobValue()')

    #############################################################################################################################
    #                                                                                                                           #
    #  UPDATE BUTTON LEDS                                                                                                       #
    #                                                                                                                           #
    #############################################################################################################################

    def UpdateLEDs(self):

        if device.isAssigned():
            # stop
            device.midiOutNewMsg(
                (0x5D << 8) + midi.TranzPort_OffOnT[transport.isPlaying() == midi.PM_Stopped], 0)
            # loop
            LoopMode = transport.getLoopMode()
            device.midiOutNewMsg((0x5A << 8) +
                                 midi.TranzPort_OffOnT[LoopMode == midi.SM_Pat], 1)
            # record
            r = transport.isRecording()
            device.midiOutNewMsg(
                (0x5F << 8) + midi.TranzPort_OffOnT[r], 2)
            # SMPTE/BEATS
            device.midiOutNewMsg(
                (0x71 << 8) + midi.TranzPort_OffOnT[ui.getTimeDispMin()], 3)
            device.midiOutNewMsg(
                (0x72 << 8) + midi.TranzPort_OffOnT[not ui.getTimeDispMin()], 4)
            # self.Page
            for m in range(0,  6):
                device.midiOutNewMsg(
                    ((0x28 + m) << 8) + midi.TranzPort_OffOnT[m == self.Page], 5 + m)
            # changed flag
            device.midiOutNewMsg(
                (0x50 << 8) + midi.TranzPort_OffOnT[general.getChangedFlag() > 0], 11)
            # metronome
            device.midiOutNewMsg(
                (0x59 << 8) + midi.TranzPort_OffOnT[general.getUseMetronome()], 12)
            # rec precount
            device.midiOutNewMsg(
                (0x58 << 8) + midi.TranzPort_OffOnT[general.getPrecount()], 13)
            # self.Scrub
            device.midiOutNewMsg((0x65 << 8) +
                                 midi.TranzPort_OffOnT[self.Scrub], 15)
            # use RUDE SOLO to show if any track is armed for recording
            b = 0
            for m in range(0,  mixer.trackCount()):
                if mixer.isTrackArmed(m):
                    b = 1 + int(r)
                    break

            device.midiOutNewMsg(
                (0x73 << 8) + midi.TranzPort_OffOnBlinkT[b], 16)
            # smoothing
            device.midiOutNewMsg(
                (0x33 << 8) + midi.TranzPort_OffOnT[self.SmoothSpeed > 0], 17)
            # self.Flip
            device.midiOutNewMsg(
                (0x32 << 8) + midi.TranzPort_OffOnT[self.Flip], 18)
            # focused windows
            device.midiOutNewMsg(
                (0x45 << 8) + midi.TranzPort_OffOnT[ui.getFocused(midi.widBrowser)], 20)
            device.midiOutNewMsg((0x3E << 8) +
                                 midi.TranzPort_OffOnT[ui.getFocused(midi.widPlaylist)], 21)
            BusLed = ui.getFocused(midi.widMixer) & (
                self.ColT[0].TrackNum >= 100)
            OutputLed = ui.getFocused(midi.widMixer) & (
                self.ColT[0].TrackNum >= 0) & (self.ColT[0].TrackNum <= 1)
            InputLed = ui.getFocused(midi.widMixer) & (
                not OutputLed) & (not BusLed)
            device.midiOutNewMsg((0x3F << 8) +
                                 midi.TranzPort_OffOnT[InputLed], 22)
            device.midiOutNewMsg((0x41 << 8) +
                                 midi.TranzPort_OffOnT[ui.getFocused(midi.widChannelRack)], 23)
            device.midiOutNewMsg((0x43 << 8) +
                                 midi.TranzPort_OffOnT[BusLed], 24)
            device.midiOutNewMsg(
                (0x44 << 8) + midi.TranzPort_OffOnT[OutputLed], 25)

            # device.midiOutNewMsg((0x4B << 8) + midi.TranzPort_OffOnT[ui.getFocused(midi.widChannelRack)], 21)
        if debug:
            print('UpdateLEDs()')



# -------------------------------------------------------------------------------------------------------------------------------
# PROCEDURES
# -------------------------------------------------------------------------------------------------------------------------------

    #############################################################################################################################
    #                                                                                                                           #
    # TRACK SELECTION                                                                                                           #
    #                                                                                                                           #
    #############################################################################################################################

    def TrackSel(self, Index, Step):
        Index = 2 - Index
        device.baseTrackSelect(Index, Step)
        if Index == 0:
            # print(channels.channelNumber)
            s = channels.getChannelName(channels.channelNumber())
            self.SendMsg2('Selected Channel: ' + s)
        elif Index == 1:
            self.SendMsg2('Selected Mixer track: ' +
                          mixer.getTrackName(mixer.trackNumber()))
        elif Index == 2:
            #if self.Shift:
            #    #open the piano roll:
            #    ui.hideWindow(midi.widPlaylist)
            #    ui.showWindow(midi.widPianoRoll)
            #    ui.setFocused(midi.widPianoRoll)
            #else:
            s = patterns.getPatternName(patterns.patternNumber())
            self.SendMsg2('Selected Pattern: ' + s)
            if transport.getLoopMode()==1:   
            # Ensure that we are in Pattern Mode:
                transport.globalTransport(midi.FPT_Loop,2) 
                patterns.selectPattern(patterns.patternNumber()) 

        if debug:
            print('TrackSel() '+str(Index) + " " + str(Step))

    #############################################################################################################################
    #                                                                                                                           #
    # PRINCIPAL JOG DIAL OPERATIONS                                                                                             #
    #                                                                                                                           #
    #############################################################################################################################
    def Jog(self, event):
        print("JOG SOURCE ="+str(self.JogSource))
        if self.JogSource == 0:
            transport.globalTransport(
                midi.FPT_Jog + int(self.Shift ^ self.Scrub), event.outEv, event.pmeFlags)  # relocate
        elif self.JogSource == 0x46:
            transport.globalTransport(
                midi.FPT_MoveJog, event.outEv, event.pmeFlags)
            self.SendMsg2(
                "Hold using JogDial to move selected item in playlist")
        elif self.JogSource == 0x48:
            if self.Shift:
                s = 'Marker selection'
            else:
                ui.showWindow(midi.widPlaylist)
                ui.setFocused(midi.widPlaylist)
                s = 'Hold MARK while using Jog Dial to navigate markers'
            if event.outEv != 0:
                if transport.globalTransport(midi.FPT_MarkerJumpJog + int(self.Shift), event.outEv, event.pmeFlags) == midi.GT_Global:
                    s = ui.getHintMsg()
            self.SendMsg2(s)

        elif self.JogSource == 0x3D:
            if event.outEv == 0:
                s = 'Undo history'
            elif transport.globalTransport(midi.FPT_UndoJog, event.outEv, event.pmeFlags) == midi.GT_Global:
                s = ui.GetHintMsg()
            self.OnSendTempMsg(
                self.ArrowsStr + s + ' (level ' + general.getUndoLevelHint() + ')', 500)

        elif self.JogSource == 0x64:
            if event.outEv != 0:
                transport.globalTransport(
                    midi.FPT_HZoomJog + int(self.Shift), event.outEv, event.pmeFlags)

        elif self.JogSource == 0x4C:

            if event.outEv != 0:
                transport.globalTransport(
                    midi.FPT_WindowJog, event.outEv, event.pmeFlags)
            # Application.ProcessMessages
            s = ui.getFocusedFormCaption()
            if s != "":
                self.SendMsg2('Current window: ' + s)

        elif (self.JogSource == 0x3F) & (event.outEv == 0):
            self.SetFirstTrack(mixer.trackNumber())
            ui.showWindow(midi.widMixer)
            ui.setFocused(midi.widMixer)

        elif (self.JogSource == 0x3E) | (self.JogSource == 0x3F):
            self.TrackSel(self.JogSource -
                          0x3E, event.outEv)
            if self.JogSource == 0x3E:
                ui.showWindow(midi.widPlaylist)
                ui.setFocused(midi.widPlaylist)
            elif self.JogSource == 0x3F:
                ui.showWindow(midi.widMixer)
                ui.setFocused(midi.widMixer)

        #elif self.JogSource == 0x41:
        #    ui.showWindow(midi.widChannelRack)
        #    ui.setFocused(midi.widChannelRack)
        #    self.TrackSel(2, event.outEv)

        elif (self.JogSource == 0x44):
            ui.showWindow(midi.widMixer)
            ui.setFocused(midi.widMixer)
            self.SetFirstTrack(0 + event.outEv)

        elif (self.JogSource == 0x43):
            ui.showWindow(midi.widMixer)
            ui.setFocused(midi.widMixer)
            x = 125
            while (x > 0):
                trackName = mixer.getTrackName(x)
                x -= 1
                if trackName.startswith('Insert '):
                    break
            self.SetFirstTrack(x+2)

        elif self.JogSource == 0x4a:
            ui.showWindow(midi.widBrowser)
            ui.setFocused(midi.widBrowser)
            self.SendMsg2("Browser Window")
            print("browser Wind")

        elif self.JogSource == 0x41:

            if event.outEv != 0:
                channels.processRECEvent(midi.REC_Tempo, channels.incEventValue(midi.REC_Tempo, event.outEv, midi.EKRes),
                                         midi.PME_RECFlagsT[int(event.pmeFlags & midi.PME_LiveInput != 0)] & (not midi.REC_FromMIDI))
            self.SendMsg2('Tempo: ' +
                          mixer.getEventIDValueString(midi.REC_Tempo, mixer.getCurrentTempo()))

        #elif self.JogSource in [0x42, 0x43, 0x44, 0x45]:
        #    # CC
        #    event.data1 = 390 + self.JogSource - 0x42

        #    if event.outEv != 0:
        #        event.isIncrement = 1
        #        s = chr(0x7E + int(event.outEv < 0))
        #        self.SendMsg2('Free jog ' +
        #                      str(event.data1) + ': ' + s)
        #        device.processMIDICC(event)
        #        return
        #    else:
        #        self.SendMsg2('Free jog ' + str(event.data1))
        self.UpdateLEDs()
        if debug:
            print('JOG() '+str(event))

    #############################################################################################################################
    #                                                                                                                           #
    #   SEND A MESSAGE TO THE FIRST DISPLAY                                                                                     #
    #                                                                                                                           #
    #############################################################################################################################

    def SendMsg(self, Msg, Row=0, Display=1):
        if Display == 1:
            sysex = self.LCD1 + bytearray(Msg, 'utf-8')
            sysex.append(0xF7)
            device.midiOutSysex(bytes(sysex))
        elif Display == 2:
            sysex = bytearray([0xF0, 0x00, 0x00, 0x67, 0x15, 0x13, (self.LastMsgLen + 1)
                               * Row]) + bytearray(Msg.ljust(self.LastMsgLen + 1, ' '), 'utf-8')
            sysex.append(0xF7)
            device.midiOutSysex(bytes(sysex))
        elif Display == 3:
            ui.setHintMsg(Msg)
        if debug:
            print('SendMsg()')

    #############################################################################################################################
    #                                                                                                                           #
    #   SEND A MESSAGE TO THE SECOND DISPLAY                                                                                    #
    #                                                                                                                           #
    #############################################################################################################################
    def SendMsg2(self, Msg, Duration=1000):
        self.SendMsg('  '+Msg.ljust(54, ' '), 0, 2)
        if debug:
            print('SendMsg2() '+Msg)

    #############################################################################################################################
    #                                                                                                                           #
    #   UPDATE THE TIME DISPLAY                                                                                                 #
    #                                                                                                                           #
    #############################################################################################################################

    def SendTimeMsg(self, Msg):
        TempMsg = bytearray(10)
        for n in range(0, len(Msg)):
            TempMsg[n] = ord(Msg[n])

        if device.isAssigned():
            # send chars that have changed
            for m in range(0, min(len(self.LastTimeMsg), len(TempMsg))):
                if self.LastTimeMsg[m] != TempMsg[m]:
                    device.midiOutMsg(midi.MIDI_CONTROLCHANGE +
                                      ((0x49 - m) << 8) + ((TempMsg[m]) << 16))

        self.LastTimeMsg = TempMsg

    #############################################################################################################################
    #                                                                                                                           #
    #  Called for short MIDI out messages sent from MIDI Out plugin.                                                            #
    #                                                                                                                           #
    #############################################################################################################################
    def SendAssignmentMsg(self, Msg):
        if (len(Msg) < 3):
            Msg = ' ' + Msg

        device.midiOutMsg(midi.MIDI_CONTROLCHANGE +
                          ((0x4B) << 8) + (ord(Msg[1]) << 16))
        device.midiOutMsg(midi.MIDI_CONTROLCHANGE +
                          ((0x4A) << 8) + (ord(Msg[2]) << 16))
        if debug:
            print('SendAssignmentMsg() '+str(Msg))

    def UpdateTempMsg(self):

        self.SendMsg(self.TempMsgT[int(self.TempMsgCount != 0)])
        if debug:
            print('UpdateTempMsg()')

    #############################################################################################################################
    #                                                                                                                           #
    #  HANDLES PRINCIPAL LOGIC FOR DISPLAYING DATA ON DISPLAYS                                                                  #
    #                                                                                                                           #
    #############################################################################################################################
    def UpdateTextDisplay(self):
        s1 = ''
        s2 = ''
        s3 = '  '
        ch = "CH"
        master = 'MASTER '
        EffectsExist = False
        if self.Page == MackieCUPage_Free:
            ch = "FR"
        elif self.Page == MackieCUPage_FX:
            ch = "FX"
        elif self.Page == MackieCUPage_EQ:
            ch = "EQ"
        for m in range(0, len(self.ColT) - 1):
            s = ''
            sa = ''
            sa2 = ''
            if self.Page == MackieCUPage_Free:
                s = '  ' + utils.Zeros(self.ColT[m].TrackNum + 1, 2, ' ')
                ch = "FR"
                master = "FR08   "
            elif self.Page == MackieCUPage_FX and self.CurPluginID == -1:
                ch = "FX"
                master = "FX08   "
                if plugins.isValid(mixer.trackNumber(), m):
                    EffectsExist = True
                    #s = DisplayName(plugins.getPluginName(self.ColT[m].TrackNum,m))
                    t = (plugins.getPluginName(mixer.trackNumber(), m)).split()
                    s = t[0][0:6]
                    if len(t) == 3:
                        # otherwise we can miss important aspects of the plugin like version number
                        t[1] = t[1]+t[2]
                    if len(t) >= 2:
                        sa = t[1][0:6].title()
                    elif (len(t) == 1 and len(t[0]) > 6):
                        sa = t[0][6:]
                        if len(sa) == 1:  # This just looks ugly so instead:
                            s = t[0][0:5]
                            sa = t[0][5:]
                    else:
                        sa = "       "
                else:
                    s = "   \\   "  # invalid
                    sa = "   \\   "
                if self.ColT[m].TrackNum > 99:
                    sa2 = ch[1]+str(self.ColT[m].TrackNum).zfill(2)+'  '
                else:
                    sa2 = 'ch'+str(self.ColT[m].TrackNum).zfill(2)+'  '
            elif self.Page == MackieCUPage_FX and self.CurPluginID > -1:  # plugin params
                t = self.ColT[m].TrackName.split()
                if len(t) > 0:
                    print(t)
                    s = t[0][0:6]
                    if len(t) == 3:
                        # otherwise we can miss important aspects of the param
                        t[1] = t[1]+t[2]
                    if len(t) >= 2:
                        sa = t[1][0:6].title()
                    elif (len(t) == 1 and len(t[0]) > 6):
                        sa = t[0][6:]
                        if len(sa) == 1:  # This just looks ugly so instead:
                            s = t[0][0:5]
                            sa = t[0][5:]
                    else:
                        sa = "       "
                else:
                    s = "      "
                    sa = "      "
            else:
                if self.ShowTrackNumbers:
                    s = mixer.getTrackName(self.ColT[m].TrackNum, 6)
                    sa = '   '+str(self.ColT[m].TrackNum)+' '
                else:
                    t = mixer.getTrackName(self.ColT[m].TrackNum, 12).split()
                    if len(t) > 0:
                        print(t)
                        s = t[0][0:6]
                        if len(t) == 3:
                            # otherwise we can miss important aspects of the name
                            t[1] = t[1]+t[2]
                        if len(t) >= 2:
                            sa = t[1][0:6].title()
                        elif (len(t) == 1 and len(t[0]) > 6):
                            sa = t[0][6:]
                            # This just looks ugly so instead:
                            if len(sa) == 1:
                                s = t[0][0:5]
                                sa = t[0][5:]
                        else:
                            sa = "       "
                    else:
                        s = "      "
                        sa = "      "

            if self.ColT[m].TrackNum > 99:
                sa2 = ch[1]+str(self.ColT[m].TrackNum).zfill(2)+'  '
            else:
                sa2 = ch+str(self.ColT[m].TrackNum).zfill(2)+'  '
            for n in range(1, 7 - len(s) + 1):
                s = s + ' '
            for n in range(1, 7 - len(sa) + 1):
                sa = sa + ' '
            s1 = s1 + s
            s2 = s2 + sa
            s3 = s3 + sa2
            if self.Page == MackieCUPage_Free:
                if self.FreeText == 0:
                    # Good for all (most) Roland Zenology Instruments
                    self.SendMsg2("(Zenology Instruments)")
                    s2 = "Cutoff  Reso   Attack Release Vibrato Decay Sust  Level"
                elif self.FreeText == 1:
                    self.SendMsg2("(Common Synth Parameters)")
                    s2 = "Cutoff  Reso   Attack  Decay  Sustain Release Vib Level"  
                elif self.FreeText == 2:
                    self.SendMsg2("(Generic Parameters)")
                    s2 = "Param1 Param2 Param3 Param4 Param5 Param6 Param7 Param8"  
                else:
                    self.SendMsg2("Blank")
                    s2 = "                                                       "  # Or maybe just blank?
            if self.Page == MackieCUPage_EQ:
                s1 = "  Low    Med    High   Low    Med   High           Reset"
                s2 = "  Freq   Freq   Freq   Width  Width Width           All "
        self.SendMsg(s1+s2)
        if (self.ColT[m].TrackNum < 9):
            self.SendMsg(s3[0:105] + master, 1, 2)
        else:
            self.SendMsg(
                s3[0:105] + 'BNK'+str(math.ceil(self.ColT[m].TrackNum/8)-1).zfill(2), 1, 2)
        if debug:
            print('UpdateTextDisplay()')

    #############################################################################################################################
    #                                                                                                                           #
    #  HANDLES UPDATING OF CHANNEL STRIPS FOR ASSIGNMENT SENDS, FX AND FREE                                                     #
    #                                                                                                                           #
    #############################################################################################################################

    def UpdateMixer_Sel(self):

        if self.Page != MackieCUPage_Free:
            if device.isAssigned():
                for m in range(0, len(self.ColT) - 1):
                    device.midiOutNewMsg(((0x18 + m) << 8) +
                                         midi.TranzPort_OffOnT[self.ColT[m].TrackNum == mixer.trackNumber()], self.ColT[m].LastValueIndex + 4)

            if self.Page in [MackieCUPage_Sends, MackieCUPage_FX]:
                self.UpdateColT()
        if debug:
            print('UpdateMixer_Sel()')

    #############################################################################################################################
    #                                                                                                                           #
    #  PRINCIPAL FUNCTION RESPONSIBLE FOR UPDATINGCOLUMNS                                                                       #
    #                                                                                                                           #
    #############################################################################################################################
    def UpdateCol(self, Num):

        data1 = 0
        data2 = 0
        baseID = 0
        center = 0
        b = False

        if device.isAssigned():
            if self.Page == MackieCUPage_Free:
                baseID = midi.EncodeRemoteControlID(
                    device.getPortNumber(), 0, self.ColT[Num].BaseEventID)
                # slider
                m = self.FreeCtrlT[self.ColT[Num].TrackNum]
                device.midiOutNewMsg(midi.MIDI_PITCHBEND + Num + ((m & 0x7F)
                                                                  << 8) + ((m >> 7) << 16), self.ColT[Num].LastValueIndex + 5)
                if Num < 8:
                    # ring
                    d = mixer.remoteFindEventValue(
                        baseID + int(self.ColT[Num].KnobHeld))
                    if d >= 0:
                        m = 1 + round(d * 10)
                    else:
                        m = int(self.ColT[Num].KnobHeld) * (11 + (2 << 4))
                    device.midiOutNewMsg(
                        midi.MIDI_CONTROLCHANGE + ((0x30 + Num) << 8) + (m << 16), self.ColT[Num].LastValueIndex)
                    # buttons
                    for n in range(0, 4):
                        d = mixer.remoteFindEventValue(baseID + 3 + n)
                        if d >= 0:
                            b = d >= 0.5
                        else:
                            b = False

                        device.midiOutNewMsg(
                            ((n * 8 + Num) << 8) + midi.TranzPort_OffOnT[b], self.ColT[Num].LastValueIndex + 1 + n)
            else:
                sv = mixer.getEventValue(self.ColT[Num].SliderEventID)

                if Num < 8:
                    # V-Pot
                    center = self.ColT[Num].KnobCenter
                    if self.ColT[Num].KnobEventID >= 0:
                        m = mixer.getEventValue(
                            self.ColT[Num].KnobEventID, midi.MaxInt, False)
                        if center < 0:
                            if self.ColT[Num].KnobResetEventID == self.ColT[Num].KnobEventID:
                                center = int(
                                    m != self.ColT[Num].KnobResetValue)
                            else:
                                center = int(
                                    sv != self.ColT[Num].KnobResetValue)

                        if self.ColT[Num].KnobMode < 2:
                            print("knobmode<2")
                            data1 = 1 + round(m * (10 / midi.FromMIDI_Max))
                        else:
                            data1 = round(m * (11 / midi.FromMIDI_Max))
                        if self.ColT[Num].KnobMode > 3:
                            print("knobmode>3")
                            data1 = (center << 6)
                        else:
                            data1 = data1 + \
                                (self.ColT[Num].KnobMode << 4) + (center << 6)
                    else:
                        data1 = 0

                        if self.Page == MackieCUPage_FX:
                            # Plugin Parameter Value
                            paramValue = plugins.getParamValue(int(
                                Num + self.PluginParamOffset), mixer.trackNumber(), int(self.CurPluginID + self.CurPluginOffset))
                            data1 = int(paramValue)
                            self.SendMsg2("To Do \\:-) ")
                            # TODO fix when getParamValue starts working

                    device.midiOutNewMsg(midi.MIDI_CONTROLCHANGE + ((0x30 + Num) << 8) + (data1 << 16), self.ColT[Num].LastValueIndex)

                    # arm, solo, mute
                    device.midiOutNewMsg(((0x00 + Num) << 8) + midi.TranzPort_OffOnBlinkT[int(mixer.isTrackArmed(
                        self.ColT[Num].TrackNum)) * (1 + int(transport.isRecording()))], self.ColT[Num].LastValueIndex + 1)
                    device.midiOutNewMsg(((0x08 + Num) << 8) + midi.TranzPort_OffOnT[mixer.isTrackSolo(
                        self.ColT[Num].TrackNum)], self.ColT[Num].LastValueIndex + 2)
                    device.midiOutNewMsg(((0x10 + Num) << 8) + midi.TranzPort_OffOnT[not mixer.isTrackEnabled(
                        self.ColT[Num].TrackNum)], self.ColT[Num].LastValueIndex + 3)

                # slider
                data1 = self.AlphaTrack_LevelToSlider(sv)
                data2 = data1 & 127
                data1 = data1 >> 7
                device.midiOutNewMsg(midi.MIDI_PITCHBEND + Num + (data2 << 8) +
                                     (data1 << 16), self.ColT[Num].LastValueIndex + 5)

            Dirty = False
        if debug:
            print('UpdateCol()')

    #############################################################################################################################
    #                                                                                                                           #
    #  PRINCIPAL PROCEDURE FOR HANDLING INTERNAL COLUMN LIST                                                                    #
    #                                                                                                                           #
    #############################################################################################################################
    def UpdateColT(self):

        f = self.FirstTrackT[self.FirstTrack]
        CurID = mixer.getTrackPluginId(mixer.trackNumber(), 0)
        for m in range(0, len(self.ColT)):
            if self.Page == MackieCUPage_Free:
                # free controls
                if m == 8:
                    self.ColT[m].TrackNum = MackieCU_nFreeTracks
                else:
                    self.ColT[m].TrackNum = (f + m) % MackieCU_nFreeTracks

                self.ColT[m].KnobName = 'Knob ' + \
                    str(self.ColT[m].TrackNum + 1)
                self.ColT[m].SliderName = 'Slider ' + \
                    str(self.ColT[m].TrackNum + 1)

                self.ColT[m].BaseEventID = self.FreeEventID + \
                    self.ColT[m].TrackNum * 8  # first virtual CC
            else:
                self.ColT[m].KnobPressEventID = -1
                ch = 'CH'+str(self.ColT[m].TrackNum).zfill(2) + ' - '

                # mixer
                if m == 8:
                    self.ColT[m].TrackNum = -2
                    self.ColT[m].BaseEventID = midi.REC_MainVol
                    self.ColT[m].SliderEventID = self.ColT[m].BaseEventID
                    self.ColT[m].SliderName = 'Master Volume'
                else:
                    self.ColT[m].TrackNum = midi.TrackNum_Master + \
                        ((f + m) % mixer.trackCount())
                    self.ColT[m].BaseEventID = mixer.getTrackPluginId(
                        self.ColT[m].TrackNum, 0)
                    self.ColT[m].SliderEventID = self.ColT[m].BaseEventID + \
                        midi.REC_Mixer_Vol
                    s = ch+mixer.getTrackName(self.ColT[m].TrackNum)
                    self.ColT[m].SliderName = s + ' - Volume'

                    self.ColT[m].KnobEventID = -1
                    self.ColT[m].KnobResetEventID = -1
                    self.ColT[m].KnobResetValue = midi.FromMIDI_Max >> 1
                    self.ColT[m].KnobName = ''
                    self.ColT[m].KnobMode = 1  # parameter, pan, volume, off
                    self.ColT[m].KnobCenter = -1

                    self.ColT[m].TrackName = ''

                    if self.Page == MackieCUPage_Pan:
                        self.ColT[m].KnobEventID = self.ColT[m].BaseEventID + \
                            midi.REC_Mixer_Pan
                        self.ColT[m].KnobResetEventID = self.ColT[m].KnobEventID
                        self.ColT[m].KnobName = mixer.getTrackName(
                            self.ColT[m].TrackNum) + ' - ' + 'Panning'
                    elif self.Page == MackieCUPage_Stereo:
                        self.ColT[m].KnobEventID = self.ColT[m].BaseEventID + \
                            midi.REC_Mixer_SS
                        self.ColT[m].KnobResetEventID = self.ColT[m].KnobEventID
                        self.ColT[m].KnobName = mixer.getTrackName(
                            self.ColT[m].TrackNum) + ' - ' + 'Separation'
                    elif self.Page == MackieCUPage_Sends:
                        self.ColT[m].KnobEventID = CurID + \
                            midi.REC_Mixer_Send_First + self.ColT[m].TrackNum
                        s = mixer.getEventIDName(self.ColT[m].KnobEventID)
                        self.ColT[m].KnobName = s
                        self.ColT[m].KnobResetValue = round(
                            12800 * midi.FromMIDI_Max / 16000)
                        self.ColT[m].KnobCenter = mixer.getRouteSendActive(
                            mixer.trackNumber(), self.ColT[m].TrackNum)
                        if self.ColT[m].KnobCenter == 0:
                            self.ColT[m].KnobMode = 4
                        else:
                            self.ColT[m].KnobMode = 2
                    elif self.Page == MackieCUPage_FX:
                        if self.CurPluginID == -1:  # Plugin not selected
                            self.ColT[m].CurID = mixer.getTrackPluginId(
                                mixer.trackNumber(), m + self.CurPluginOffset)
                            self.ColT[m].KnobEventID = self.ColT[m].CurID + \
                                midi.REC_Plug_MixLevel
                            s = mixer.getEventIDName(self.ColT[m].KnobEventID)
                            self.ColT[m].KnobName = s
                            self.ColT[m].KnobResetValue = midi.FromMIDI_Max

                            IsValid = mixer.isTrackPluginValid(
                                mixer.trackNumber(), m + self.CurPluginOffset)
                            IsEnabledAuto = mixer.isTrackAutomationEnabled(
                                mixer.trackNumber(), m + self.CurPluginOffset)
                            if IsValid:
                                self.ColT[m].KnobMode = 2
                                #self.ColT[m].KnobEventID = self.ColT[m].CurID + midi.REC_Plug
                                #self.ColT[m].KnobPressEventID = self.ColT[m].CurID + midi.REC_Plug_Mute

                                self.ColT[m].TrackName = plugins.getPluginName(mixer.trackNumber(), m + self.CurPluginOffset)
                            else:
                                self.ColT[m].KnobMode = 4
                            self.ColT[m].KnobCenter = int(IsValid & IsEnabledAuto)
                        else:  # Plugin selected
                            self.ColT[m].CurID = mixer.getTrackPluginId(
                                mixer.trackNumber(), m + self.CurPluginOffset)
                            if m + self.PluginParamOffset < plugins.getParamCount(mixer.trackNumber(), self.CurPluginID + self.CurPluginOffset):
                                self.ColT[m].TrackName = plugins.getParamName(m + self.PluginParamOffset, mixer.trackNumber(), self.CurPluginID + self.CurPluginOffset)
                                #print("plugin Param:"+self.ColT[m].TrackName)
                                #print("plugin value:"+str(plugins.getParamValue(m + self.PluginParamOffset, mixer.trackNumber(), self.CurPluginID + self.CurPluginOffset)))
                                #print(plugins.getParamValue(m + self.PluginParamOffset, mixer.trackNumber(), self.CurPluginID + self.CurPluginOffset))
                                #plugins.setParamValue(0,m + self.PluginParamOffset, mixer.trackNumber(), self.CurPluginID + self.CurPluginOffset)
                            self.ColT[m].KnobMode = 2
                            self.ColT[m].KnobEventID = -1
                            print(self.ColT[m].TrackName)

                    elif self.Page == MackieCUPage_EQ:
                        if m < 3:
                            # gain & freq
                            self.ColT[m].SliderEventID = CurID + \
                                midi.REC_Mixer_EQ_Gain + m
                            self.ColT[m].KnobResetEventID = self.ColT[m].SliderEventID
                            s = mixer.getEventIDName(
                                self.ColT[m].SliderEventID)
                            self.ColT[m].SliderName = s
                            self.ColT[m].KnobEventID = CurID + \
                                midi.REC_Mixer_EQ_Freq + m
                            s = mixer.getEventIDName(self.ColT[m].KnobEventID)
                            self.ColT[m].KnobName = s
                            self.ColT[m].KnobResetValue = midi.FromMIDI_Max >> 1
                            self.ColT[m].KnobCenter = -2
                            self.ColT[m].KnobMode = 0
                        else:
                            if m < 6:
                                # Q
                                self.ColT[m].SliderEventID = CurID + \
                                    midi.REC_Mixer_EQ_Q + m - 3
                                self.ColT[m].KnobResetEventID = self.ColT[m].SliderEventID
                                s = mixer.getEventIDName(
                                    self.ColT[m].SliderEventID)
                                self.ColT[m].SliderName = s
                                self.ColT[m].KnobEventID = self.ColT[m].SliderEventID
                                self.ColT[m].KnobName = self.ColT[m].SliderName
                                self.ColT[m].KnobResetValue = 17500
                                self.ColT[m].KnobCenter = -1
                                self.ColT[m].KnobMode = 2
                            else:
                                self.ColT[m].SliderEventID = -1
                                self.ColT[m].KnobEventID = -1
                                self.ColT[m].KnobMode = 4

                    # self.Flip knob & slider
                    if self.Flip:
                        self.ColT[m].KnobEventID, self.ColT[m].SliderEventID = utils.SwapInt(
                            self.ColT[m].KnobEventID, self.ColT[m].SliderEventID)
                        s = self.ColT[m].SliderName
                        self.ColT[m].SliderName = self.ColT[m].KnobName
                        self.ColT[m].KnobName = s
                        self.ColT[m].KnobMode = 2
                        if not (self.Page in [MackieCUPage_Sends, MackieCUPage_FX, MackieCUPage_EQ]):
                            self.ColT[m].KnobCenter = -1
                            self.ColT[m].KnobResetValue = round(
                                12800 * midi.FromMIDI_Max / 16000)
                            self.ColT[m].KnobResetEventID = self.ColT[m].KnobEventID

            self.ColT[m].LastValueIndex = 48 + m * 6
            self.ColT[m].Peak = 0
            self.ColT[m].ZPeak = False
            self.UpdateCol(m)
        if debug:
            print('UpdateColT()')

    def SetJogSource(self, Value):

        self.JogSource = Value
        if debug:
            print('SetJogSource()')

    def OnWaitingForInput(self):

        self.SendTimeMsg('..........')
        if debug:
            print('OnWaitingForInput()')

    def UpdateClicking(self):  # switch self.Clicking for transport buttons

        if device.isAssigned():
            device.midiOutSysex(
                bytes([0xF0, 0x00, 0x00, 0x66, 0x14, 0x0A, int(self.Clicking), 0xF7]))
        if debug:
            print('UpdateClicking()')
    # set backlight timeout (0 should switch off immediately, but doesn't really work well)

    def SetBackLight(self, Minutes):
        if device.isAssigned():
            device.midiOutSysex(bytes([0xF0, 0x00, 0x00, 0x66, 0x14, 0x0B, Minutes, 0xF7]))
        if debug:
            print('SetBackLight()')
    #############################################################################################################################
    #                                                                                                                           #
    #  HANDLES THE DISPLAY METERS                                                                                                #
    #                                                                                                                           #
    #############################################################################################################################

    def UpdateMeterMode(self):

        # force vertical (activity) meter mode for free controls self.Page
        if self.Page == MackieCUPage_Free:
            self.CurMeterMode = 1
        else:
            self.CurMeterMode = self.MeterMode

        if device.isAssigned():
            # clear peak indicators
            for m in range(0, len(self.ColT) - 1):
                device.midiOutMsg(midi.MIDI_CHANAFTERTOUCH +
                                  (0xF << 8) + (m << 12))
            # disable all meters
            for m in range(0, 8):
                device.midiOutSysex(
                    bytes([0xF0, 0x00, 0x00, 0x66, 0x14, 0x20, m, 0, 0xF7]))


        # reset stuff
        if self.CurMeterMode > 0:
            self.TempMsgCount = -1
        else:
            self.TempMsgCount = 500 // 48 + 1

        # $D for horizontal, $E for vertical meters
        self.MeterMax = 0xD + int(self.CurMeterMode == 1)
        self.ActivityMax = 0xD - int(self.CurMeterMode == 1) * 6

        if device.isAssigned():
            # device.midiOutSysex(bytes(bytearray([0xd1, 0xD, 0xF7])))
            # device.midiOutSysex(bytes(bytearray([0xd1, 0xD+16, 0xF7])))
            # horizontal/vertical meter mode
            device.midiOutSysex(
                bytes([0xF0, 0x00, 0x00, 0x66, 0x14, 0x21, int(self.CurMeterMode > 0), 0xF7]))

            # enable all meters
            if self.CurMeterMode == 2:
                n = 1
            else:
                n = 1 + 2
            for m in range(0, 8):
                device.midiOutSysex(bytes([0xF0, 0x00, 0x00, 0x66, 0x14, 0x20, m, n, 0xF7]))
 
        if debug:
            print('UpdateMeterMode()')
    #############################################################################################################################
    #                                                                                                                           #
    #  HANDLES ASSIGNMENT SELECTION (PLUS CRUDE EXTENDER POSITIONING)                                                            #
    #                                                                                                                           #
    #############################################################################################################################

    def SetPage(self, Value):
        oldPage = self.Page
        self.Page = Value

        self.FirstTrack = int(self.Page == MackieCUPage_Free)
        receiverCount = device.dispatchReceiverCount()
        if receiverCount == 0:
            self.SetFirstTrack(self.FirstTrackT[self.FirstTrack])
        elif self.Page == oldPage:
            if self.ExtenderPos == ExtenderLeft:
                for n in range(0, receiverCount):
                    device.dispatch(n, midi.MIDI_NOTEON + (0x7F << 8) +
                                    (self.FirstTrackT[self.FirstTrack] + (n * 8) << 16))
                self.SetFirstTrack(
                    self.FirstTrackT[self.FirstTrack] + receiverCount * 8)
            elif self.ExtenderPos == ExtenderRight:
                self.SetFirstTrack(self.FirstTrackT[self.FirstTrack])
                for n in range(0, receiverCount):
                    device.dispatch(n, midi.MIDI_NOTEON + (0x7F << 8) +
                                    (self.FirstTrackT[self.FirstTrack] + ((n + 1) * 8) << 16))

        if self.Page == MackieCUPage_Free:

            BaseID = midi.EncodeRemoteControlID(
                device.getPortNumber(), 0, self.FreeEventID + 7)
            for n in range(0,  len(self.FreeCtrlT)):
                d = mixer.remoteFindEventValue(BaseID + n * 8, 1)
                if d >= 0:
                    self.FreeCtrlT[n] = min(round(d * 16384), 16384)
            # Toggle options for  Free Controls Text
            if self.Shift:
                if self.FreeText == 0:
                    self.FreeText = 1
                elif self.FreeText == 1:
                    self.FreeText = 2
                elif self.FreeText == 2:
                        self.FreeText = -1
                else:
                    self.FreeText = 0

        if (oldPage == MackieCUPage_Free) | (self.Page == MackieCUPage_Free):
            self.UpdateMeterMode()

        self.CurPluginID = -1
        self.CurPluginOffset = 0

        self.UpdateColT()
        self.UpdateLEDs()
        self.UpdateTextDisplay()
        if debug:
            print('SetPage() '+str(Value))

    #############################################################################################################################
    #                                                                                                                           #
    #  SETS UP THE FIRST TRACK AFTER TRACK RELATED MOVEMENT OPERATIONS ARE CARRIED OUT                                          #
    #                                                                                                                           #
    #############################################################################################################################
    def SetFirstTrack(self, Value):

        if self.Page == MackieCUPage_Free:
            self.FirstTrackT[self.FirstTrack] = (
                Value + MackieCU_nFreeTracks) % MackieCU_nFreeTracks
            s = utils.Zeros(self.FirstTrackT[self.FirstTrack] + 1, 2, ' ')
        else:
            self.FirstTrackT[self.FirstTrack] = (
                Value + mixer.trackCount()) % mixer.trackCount()
            s = utils.Zeros(self.FirstTrackT[self.FirstTrack], 2, ' ')
        self.UpdateColT()
        self.SendAssignmentMsg(s)
        device.hardwareRefreshMixerTrack(-1)
        if debug:
            print('SetFirstTrack() '+str(Value))


MackieCU = TMackieCU()


def OnInit():
    MackieCU.OnInit()


def OnDeInit():
    MackieCU.OnDeInit()


def OnDirtyMixerTrack(SetTrackNum):
    MackieCU.OnDirtyMixerTrack(SetTrackNum)


def OnRefresh(Flags):
    MackieCU.OnRefresh(Flags)


def OnMidiMsg(event):
    MackieCU.OnMidiMsg(event)


def SendMsg2(Msg, Duration=1000):
    MackieCU.SendMsg2(Msg, Duration)


def OnUpdateBeatIndicator(Value):
    MackieCU.OnUpdateBeatIndicator(Value)


def OnUpdateMeters():
    MackieCU.OnUpdateMeters()


def OnIdle():
    MackieCU.OnIdle()


def OnWaitingForInput():
    MackieCU.OnWaitingForInput()
