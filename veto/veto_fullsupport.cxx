// contains a model of full support structure made of steel of sbt
// No SBT (no LiSc, ribs, walls), only a steel housing made of straight beams
// with a cross section of 15.5 mm x 240 mm around the He balloon:
//  - frames (4 beams each) at every 6th former vertical rib, z = 0 ... 50 m
//  - longitudinal beams on top/bottom at the former longitudinal rib positions
//  - one beam in each of the 4 corners

// SPDX-License-Identifier: LGPL-3.0-or-later
// SPDX-FileCopyrightText: Copyright CERN for the benefit of the SHiP
// Collaboration

// 09/07/2024
// SBT software contact: anupama.reghunath@cern.ch
/**
 * @file veto_fullsupport.cxx
 * @brief Implementation of the Veto detector class.
 *
 * This file contains the definitions for the Veto class used in the
 * FairShip Software. The class is responsible for simulating the Decay
 * Vessel(helium) + integrated SBT geometry and interactions.
 */

#include "veto.h"

#include <cmath>
#include <iostream>
#include <vector>

#include "FairGeoBuilder.h"
#include "FairGeoInterface.h"
#include "FairGeoLoader.h"
#include "FairGeoMedia.h"
#include "FairGeoNode.h"
#include "FairGeoVolume.h"
#include "FairLogger.h"  /// for FairLogger, MESSAGE_ORIGIN
#include "FairRootManager.h"
#include "FairRun.h"
#include "FairRuntimeDb.h"
#include "FairVolume.h"
#include "ShipDetectorList.h"
#include "ShipGeoUtil.h"
#include "ShipStack.h"
#include "TClonesArray.h"
#include "TGeoArb8.h"
#include "TGeoBBox.h"
#include "TGeoBoolNode.h"
#include "TGeoCompositeShape.h"
#include "TGeoCone.h"
#include "TGeoEltu.h"
#include "TGeoManager.h"
#include "TGeoMaterial.h"
#include "TGeoShapeAssembly.h"
#include "TGeoSphere.h"
#include "TGeoTube.h"
#include "TMath.h"
#include "TParticle.h"
#include "TVirtualMC.h"
#include "vetoPoint.h"

constexpr Double_t cm = 1;         // cm
constexpr Double_t m = 100 * cm;   //  m
constexpr Double_t mm = 0.1 * cm;  //  mm

// steel beams: kBeamThickness x kBeamHeight cross section
constexpr Double_t kBeamThickness = 15.5 * mm;
constexpr Double_t kBeamHeight = 240 * mm;
// a steel frame at every kSteelRibInterval-th former vertical rib
constexpr int kSteelRibInterval = 6;

/**
 * @brief Constructor for the Veto class.
 *
 * Initializes the veto detector with the given parameters.
 *
 */
veto::veto()
    : SHiP::Detector<vetoPoint>("Veto", kTRUE, kVETO),
      fFastMuon(kFALSE),
      fFollowMuon(kFALSE) {
  fUseSupport = 1;
  fLiquidVeto = 1;
}

TGeoVolume* veto::make_geo_trapezoid(
    const TString& xname, Double_t z_thick, Double_t x_thick_start,
    Double_t x_thick_end, Double_t y_thick_start, Double_t y_thick_end,
    Int_t color, TGeoMedium* material, Bool_t sens = kFALSE) {
  Double_t dz = z_thick / 2;
  Double_t dx1 = x_thick_start / 2 - 1.E-6;
  Double_t dx2 = x_thick_end / 2 - 1.E-6;
  Double_t dy1 = y_thick_start / 2 - 1.E-6;
  Double_t dy2 = y_thick_end / 2 - 1.E-6;
  TGeoArb8* T1 = new TGeoArb8("T1" + xname, dz + 1.E-6);
  T1->SetVertex(0, -dx1, -dy1);
  T1->SetVertex(1, -dx1, dy1);
  T1->SetVertex(2, dx1, dy1);
  T1->SetVertex(3, dx1, -dy1);
  T1->SetVertex(4, -dx2, -dy2);
  T1->SetVertex(5, -dx2, dy2);
  T1->SetVertex(6, dx2, dy2);
  T1->SetVertex(7, dx2, -dy2);

  TGeoVolume* T = new TGeoVolume(xname, T1, material);
  T->SetLineColor(color);
  if (sens) {
    AddSensitiveVolume(T);
  }  // and make the volumes sensitive..
  return T;
}

double veto::wx(double z) {  // calculate x thickness at z

  double wx1 = VetoStartInnerX;
  double wx2 = VetoEndInnerX;
  double z1 = 0 * m;
  double z2 = 50 * m;

  return (wx1 + (z - z1) * (wx2 - wx1) / (z2 - z1));
}

double veto::wy(double z) {  // calculate y thickness at z

  double wy1 = VetoStartInnerY;
  double wy2 = VetoEndInnerY;
  double z1 = 0 * m;
  double z2 = 50 * m;

  return (wy1 + (z - z1) * (wy2 - wy1) / (z2 - z1));
}

namespace {
/// straight steel beam (box) with half lengths dx, dy, dz
TGeoVolume* make_beam(const TString& xname, double dx, double dy, double dz,
                      Int_t color, TGeoMedium* material) {
  TGeoVolume* T = new TGeoVolume(xname, new TGeoBBox(dx, dy, dz), material);
  T->SetLineColor(color);
  return T;
}
}  // namespace

TGeoVolume* veto::make_segments() {
  TGeoVolumeAssembly* tTankVol = new TGeoVolumeAssembly("T2");

  Double_t cell_thickness_z0 =
      800 * mm;  // length of the first cell along z (800mm) 2024 version
  Double_t cell_thickness_z =
      820 * mm;  // length of the cell along z (820mm) 2024 version

  int nx = 2;  // number of longitudinal beams on top and on bottom

  // wall, scintillator and rib dimensions of the former SBT are only used as
  // reference coordinates for placing the steel beams
  double wall_thickness = f_InnerSupportThickness;
  double lisc_thickness = f_VetoThickness;
  double rib_thickness = f_RibThickness;

  const double z_start = 0 * m;
  const double z_end = 50 * m;

  TGeoMedium* steelMed = gGeoManager->GetMedium("steel");
  const int beamColor = 15;

  TGeoVolumeAssembly* frames = new TGeoVolumeAssembly("VetoSteelFrame");
  TGeoVolumeAssembly* longit_beams =
      new TGeoVolumeAssembly("VetoSteelLongitBeam");
  TGeoVolumeAssembly* corner_beams =
      new TGeoVolumeAssembly("VetoSteelCornerBeam");

  /// z positions of the former vertical ribs: z = 0 (block 1) and every cell
  /// of block 2, including the closing rib at z_end
  std::vector<double> z_ribs = {z_start};
  const double z_block2 = z_start + cell_thickness_z0;
  const int nCells =
      static_cast<int>(std::lround((z_end - z_block2) / cell_thickness_z));
  for (int iz = 0; iz <= nCells; ++iz) {
    z_ribs.push_back(z_block2 + iz * cell_thickness_z);
  }
  // steel frames at z = 0 and at every kSteelRibInterval-th rib of block 2
  auto isFrame = [](size_t k) {
    return k == 0 || (k - 1) % kSteelRibInterval == 0;
  };

  TString name("");

  /// steel frames: side beams over the full outer height, top/bottom beams
  /// in between; inner edge at the former inner wall
  for (size_t k = 0; k < z_ribs.size(); ++k) {
    if (!isFrame(k)) continue;
    const double zf = z_ribs[k];
    const double zc = zf + kBeamThickness / 2;
    const double ax = wx(zc) / 2 + wall_thickness;  // inner half width
    const double ay = wy(zc) / 2 + wall_thickness;  // inner half height

    name.Form("SteelFrameSide_z%d", static_cast<int>(zf));
    TGeoVolume* side = make_beam(name, kBeamHeight / 2, ay + kBeamHeight,
                                 kBeamThickness / 2, beamColor, steelMed);
    name.Form("SteelFrameTopBottom_z%d", static_cast<int>(zf));
    TGeoVolume* topbottom = make_beam(name, ax, kBeamHeight / 2,
                                      kBeamThickness / 2, beamColor, steelMed);

    const double xs = ax + kBeamHeight / 2;
    const double yt = ay + kBeamHeight / 2;
    frames->AddNode(side, 1, new TGeoTranslation(xs, 0, zc));
    frames->AddNode(side, 2, new TGeoTranslation(-xs, 0, zc));
    frames->AddNode(topbottom, 1, new TGeoTranslation(0, yt, zc));
    frames->AddNode(topbottom, 2, new TGeoTranslation(0, -yt, zc));
  }

  /// longitudinal and corner beams: one straight piece per former cell,
  /// parallel to z, positioned with the cross section at the downstream end
  /// of the cell so that it does not overlap with the widening balloon
  for (size_t k = 0; k + 1 < z_ribs.size(); ++k) {
    const double zb1 = z_ribs[k] + (isFrame(k) ? kBeamThickness : 0);
    const double zb2 = z_ribs[k + 1];
    const double zm = (zb1 + zb2) / 2;
    const double dz = (zb2 - zb1) / 2;
    const double ax = wx(zb2) / 2 + wall_thickness;  // inner half width
    const double ay = wy(zb2) / 2 + wall_thickness;  // inner half height
    // all top/bottom beams on one level, inner edge at the former inner wall
    const double yl = ay + kBeamHeight / 2;

    // top/bottom: centred on the former longitudinal ribs
    name.Form("SteelLongitBeam_z%d", static_cast<int>(z_ribs[k]));
    TGeoVolume* lb = make_beam(name, kBeamThickness / 2, kBeamHeight / 2, dz,
                               beamColor, steelMed);
    const double x_width = wx(zb2) + 2 * (wall_thickness + lisc_thickness);
    const double x_step = (x_width - nx * rib_thickness) / (nx + 1);
    for (int j = 0; j < nx; ++j) {
      const double xl = x_width / 2 - (j + 1) * x_step - j * rib_thickness -
                        rib_thickness / 2;
      longit_beams->AddNode(lb, 2 * j + 1, new TGeoTranslation(xl, yl, zm));
      longit_beams->AddNode(lb, 2 * j + 2, new TGeoTranslation(-xl, -yl, zm));
    }

    // corners: x centre at half the scintillator thickness from the inner
    // corner, oriented and levelled like the top/bottom longitudinal beams
    name.Form("SteelCornerBeam_z%d", static_cast<int>(z_ribs[k]));
    TGeoVolume* cb = make_beam(name, kBeamThickness / 2, kBeamHeight / 2, dz,
                               beamColor, steelMed);
    const double xc = ax + lisc_thickness / 2;
    const double yc = yl;
    corner_beams->AddNode(cb, 1, new TGeoTranslation(xc, yc, zm));
    corner_beams->AddNode(cb, 2, new TGeoTranslation(-xc, yc, zm));
    corner_beams->AddNode(cb, 3, new TGeoTranslation(-xc, -yc, zm));
    corner_beams->AddNode(cb, 4, new TGeoTranslation(xc, -yc, zm));
  }

  /// decay medium nested in the He balloon (no inner wall)
  const double balloon_thickness = f_he_balloon_thickness;
  TGeoVolume* vessel = nullptr;  // balloon (or decay medium)
  TGeoVolume* decay_medium = nullptr;
  if (balloon_thickness > 0) {
    vessel =
        make_geo_trapezoid("HeBalloon", z_end - z_start, wx(z_start), wx(z_end),
                           wy(z_start), wy(z_end), kGreen, f_he_balloon_med);
    decay_medium = make_geo_trapezoid(
        "decay_medium", (z_end - z_start) - 2 * balloon_thickness,
        wx(z_start + balloon_thickness) - 2 * balloon_thickness,
        wx(z_end - balloon_thickness) - 2 * balloon_thickness,
        wy(z_start + balloon_thickness) - 2 * balloon_thickness,
        wy(z_end - balloon_thickness) - 2 * balloon_thickness, 1,
        decayVolumeMed);
    vessel->AddNode(decay_medium, 0);
  } else {
    decay_medium = make_geo_trapezoid("decay_medium", z_end - z_start,
                                      wx(z_start), wx(z_end), wy(z_start),
                                      wy(z_end), 1, decayVolumeMed);
    vessel = decay_medium;
  }
  decay_medium->SetVisibility(kFALSE);
  tTankVol->AddNode(vessel, 0,
                    new TGeoTranslation(0, 0, (z_start + z_end) / 2));

  tTankVol->AddNode(frames, 0, new TGeoTranslation(0, 0, 0));
  tTankVol->AddNode(longit_beams, 0, new TGeoTranslation(0, 0, 0));
  tTankVol->AddNode(corner_beams, 0, new TGeoTranslation(0, 0, 0));

  return tTankVol;
}

// -------------------------------------------------------------------------
/**
 * @brief Processes a hit in the veto detector.
 *
 * This method is called whenever a hit is registered in the veto detector.
 * It processes the hit information and records the relevant data.
 *
 * @param x X-coordinate of the hit.
 * @param y Y-coordinate of the hit.
 * @param z Z-coordinate of the hit.
 * @param time Time of the hit.
 * @param energy Energy deposited by the hit.
 * @return True if the hit was processed successfully, false otherwise.
 */
Bool_t veto::ProcessHits(FairVolume* vol) {
  /** This method is called from the MC stepping */
  // Set parameters at entrance of volume. Reset ELoss.
  if (gMC->IsTrackEntering()) {
    fELoss = 0.;
    fTime = gMC->TrackTime() * 1.0e09;
    fLength = gMC->TrackLength();
    gMC->TrackPosition(fPos);
    gMC->TrackMomentum(fMom);
  }
  // Sum energy loss for all steps in the active volume
  fELoss += gMC->Edep();

  // Create vetoPoint at exit of active volume
  if (gMC->IsTrackExiting() || gMC->IsTrackStop() ||
      gMC->IsTrackDisappeared()) {
    if (fELoss == 0.) {
      return kFALSE;
    }

    fTrackID = gMC->GetStack()->GetCurrentTrackNumber();
    fEventID = gMC->CurrentEvent();
    Int_t veto_uniqueId;
    gMC->CurrentVolID(veto_uniqueId);
    TParticle* p = gMC->GetStack()->GetCurrentTrack();
    Int_t pdgCode = p->GetPdgCode();
    TLorentzVector pos;
    gMC->TrackPosition(pos);
    TLorentzVector Mom;
    gMC->TrackMomentum(Mom);
    Double_t xmean = (fPos.X() + pos.X()) / 2.;
    Double_t ymean = (fPos.Y() + pos.Y()) / 2.;
    Double_t zmean = (fPos.Z() + pos.Z()) / 2.;
    AddHit(fEventID, fTrackID, veto_uniqueId, TVector3(xmean, ymean, zmean),
           TVector3(fMom.Px(), fMom.Py(), fMom.Pz()), fTime, fLength, fELoss,
           pdgCode, TVector3(pos.X(), pos.Y(), pos.Z()),
           TVector3(Mom.Px(), Mom.Py(), Mom.Pz()));

    // Increment number of veto det points in TParticle
    ShipStack* stack = dynamic_cast<ShipStack*>(gMC->GetStack());
    stack->AddPoint(kVETO);
  }

  return kTRUE;
}

void veto::PreTrack() {
  if (!fFastMuon) {
    return;
  }
  if (TMath::Abs(gMC->TrackPid()) != 13) {
    gMC->StopTrack();
  }
}

/**
 * @brief Constructs the detector geometry.
 *
 * This function is responsible for setting up the geometry of the
 * DecayVolume+SBT detector. It is called during the detector's construction
 * phase.
 */

void veto::ConstructGeometry() {
  TGeoVolume* top = gGeoManager->GetTopVolume();

  ShipGeo::InitMedium(supportMedOut_name.Data());
  ShipGeo::InitMedium(supportMedIn_name.Data());
  ShipGeo::InitMedium(vetoMed_name.Data());
  ShipGeo::InitMedium(decayVolumeMed_name.Data());
  ShipGeo::InitMedium(f_he_balloon_med_name.Data());
  ShipGeo::InitMedium("steel");

  gGeoManager->SetNsegments(100);

  vetoMed = gGeoManager->GetMedium(
      vetoMed_name);  //! medium of veto counter, liquid or plastic scintillator
  supportMedIn = gGeoManager->GetMedium(
      supportMedIn_name);  //! medium of support structure, iron, balloon
  supportMedOut = gGeoManager->GetMedium(
      supportMedOut_name);  //! medium of support structure, aluminium, balloon
  decayVolumeMed = gGeoManager->GetMedium(
      decayVolumeMed_name);  // decay volume, air/helium/vacuum
  f_he_balloon_med =
      gGeoManager->GetMedium(f_he_balloon_med_name);  // He Balloon medium, pvc
  LOG(info) << "veto: Decay Volume medium set as: " << decayVolumeMed_name;
  TGeoVolume* tDecayVol = new TGeoVolumeAssembly("DecayVolume");

  TGeoVolume* seg = make_segments();
  tDecayVol->AddNode(seg, 1, new TGeoTranslation(0, 0, 0));
  top->AddNode(tDecayVol, 1, new TGeoTranslation(0, 0, zStartDecayVol));  //));

  // only for fastMuon simulation, otherwise output becomes too big
  if (fFastMuon && fFollowMuon) {
    const char* Vol = "TGeoVolume";
    const char* Cavern = "Cavern";
    const char* Ain = "AbsorberAdd";
    const char* Aout = "AbsorberAddCore";
    TObjArray* volumelist = gGeoManager->GetListOfVolumes();
    int lastvolume = volumelist->GetLast();
    int volumeiterator = 0;
    while (volumeiterator <= lastvolume) {
      const char* volumename = volumelist->At(volumeiterator)->GetName();
      const char* classname = volumelist->At(volumeiterator)->ClassName();
      if (strstr(classname, Vol)) {
        if (strstr(volumename, Cavern) || strstr(volumename, Ain) ||
            strstr(volumename, Aout)) {
          AddSensitiveVolume(gGeoManager->GetVolume(volumename));
          LOG(info) << "veto: made sensitive for following muons: "
                    << volumename;
        }
      }
      volumeiterator++;
    }
  }
}
