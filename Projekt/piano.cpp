#include <windows.h>
#include <conio.h>
#include <vector>
#include <map>
#include <iostream>
#include <thread>
#include <cmath>
#include <algorithm>

// beep
void PlayTone(int frequency, int duration) {
    Beep(frequency, duration);
}


void DrawKey(HDC hdc, int x, int y, int width, int height, const char* label, COLORREF color) {
    //pozadina
    HBRUSH brush = CreateSolidBrush(color);
    HPEN pen = CreatePen(PS_SOLID, 1, RGB(175, 175, 175));
    SelectObject(hdc, brush);
    SelectObject(hdc, pen);
    Rectangle(hdc, x, y, x + width, y + height);
    
    // obrub
    MoveToEx(hdc, x, y, NULL);
    LineTo(hdc, x + width, y);
    LineTo(hdc, x + width, y + height);
    LineTo(hdc, x, y + height);
    LineTo(hdc, x, y);
    
    // tipka na tipkovnici
    SetBkMode(hdc, TRANSPARENT);
    SetTextColor(hdc, RGB(0, 0, 0));
    RECT rect = {x, y + height - 30, x + width, y + height};
    DrawTextA(hdc, label, -1, &rect, DT_CENTER | DT_VCENTER | DT_SINGLELINE);
    
    // alokacija
    DeleteObject(brush);
    DeleteObject(pen);
}

int main() {
    // console prozor
    HWND console = GetConsoleWindow();
    SetWindowTextA(console, "Piano Simulator");
    MoveWindow(console, 100, 100, 800, 500, TRUE);
    
    // mapiranje frekvecnija sa notama
    std::vector<char> keys = {'A','S','D','F','G','H','J','K','L','Y','X','C','V'};
    std::map<char, int> freqs = {
        {'A', 220}, {'S', 247}, {'D', 262}, {'F', 294}, {'G', 330},
        {'H', 349}, {'J', 392}, {'K', 440}, {'L', 494}, {'Y', 523},
        {'X', 587}, {'C', 659}, {'V', 740}
    };
    
    
    HDC hdc = GetDC(console);
    
    
    HFONT hFont = CreateFont(24, 0, 0, 0, FW_BOLD, FALSE, FALSE, FALSE, DEFAULT_CHARSET, 
                            OUT_OUTLINE_PRECIS, CLIP_DEFAULT_PRECIS, CLEARTYPE_QUALITY, 
                            VARIABLE_PITCH, TEXT("Arial"));
    SelectObject(hdc, hFont);
    
    //crtanje
    system("cls");
    
    // Naslov
    SetTextColor(hdc, RGB(70, 130, 180));
    SetBkMode(hdc, TRANSPARENT);
    RECT titleRect = {0, 10, 800, 50};
    DrawTextA(hdc, "PIANO SIMULATOR", -1, &titleRect, DT_CENTER);
    
    // Instrukcije
    SetTextColor(hdc, RGB(70, 130, 180));
    RECT instrRect = {0, 400, 800, 450};
    DrawTextA(hdc, "Press keys: A,S,D,F,G,H,J,K,L,Y,X,C,V  |  ESC to exit", -1, &instrRect, DT_CENTER);
    
    // Crtaj tipke
    int keyWidth = 50;
    int keyHeight = 200;
    int startX = (800 - (keys.size() * keyWidth)) / 2;
    int startY = 100;
    
    for (int i = 0; i < keys.size(); i++) {
        DrawKey(hdc, startX + i * keyWidth, startY, keyWidth, keyHeight, 
                std::string(1, keys[i]).c_str(), RGB(255, 255, 255));
    }
    
    // crtanje imena noti
    const char* noteNames[] = {"C4", "D4", "E4", "F4", "G4", "A4", "B4", "C5", "D5", "E5", "F5", "G5", "A5"};
    SetTextColor(hdc, RGB(70, 130, 180));
    for (int i = 0; i < keys.size(); i++) {
        RECT noteRect = {startX + i * keyWidth, startY + keyHeight + 10, 
                         startX + i * keyWidth + keyWidth, startY + keyHeight + 40};
        DrawTextA(hdc, noteNames[i], -1, &noteRect, DT_CENTER);
    }
    
    
    HBRUSH brush = CreateSolidBrush(RGB(240, 248, 255));
    SelectObject(hdc, brush);
    Rectangle(hdc, 0, 70, 800, 90);
    DeleteObject(brush);
    
    
    while (true) {
        if (_kbhit()) {
            char ch = _getch();
            if (ch == 27) break;  // ako je esc stisnut, prekidaj
            
            ch = toupper(ch);
            auto it = freqs.find(ch);
            
            if (it != freqs.end()) {
                // nadji index
                int keyIndex = std::distance(keys.begin(), std::find(keys.begin(), keys.end(), ch));
                
                // mijenjanje boje tipki 
                DrawKey(hdc, startX + keyIndex * keyWidth, startY, keyWidth, keyHeight, 
                        std::string(1, ch).c_str(), RGB(173, 216, 230));
                
                // poziv na funkciju playtone
                std::thread t(PlayTone, it->second, 100);
                t.detach();
                
                // delay da ne zvuci toliko uzas
                Sleep(50);
                
                // vracanje tipke na bijelu boju
                DrawKey(hdc, startX + keyIndex * keyWidth, startY, keyWidth, keyHeight, 
                        std::string(1, ch).c_str(), RGB(255, 255, 255));
            }
        }
        
        // Sponovni delay radi buga u mijenjanju boja
        Sleep(10);
    }
    
    // alokacija ponovno
    ReleaseDC(console, hdc);
    DeleteObject(hFont);
    return 0;
}
