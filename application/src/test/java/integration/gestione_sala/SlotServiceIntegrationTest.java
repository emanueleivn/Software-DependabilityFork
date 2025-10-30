package integration.gestione_sala;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.sottosistemi.gestione_sala.service.SlotService;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import unit.test_DAO.DatabaseSetupForTest;

import java.sql.Connection;
import java.sql.Statement;
import java.time.LocalDate;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

class SlotServiceIntegrationTest {
    private SlotService slotService;

    @BeforeAll
    static void globalSetup() {
        DatabaseSetupForTest.configureH2DataSource();
    }

    private void cleanAndSeed() {
        try (Connection conn = DataSourceSingleton.getInstance().getConnection();
             Statement stmt = conn.createStatement()) {

            stmt.execute("SET REFERENTIAL_INTEGRITY FALSE");
            stmt.execute("DELETE FROM posto_proiezione");
            stmt.execute("DELETE FROM prenotazione");
            stmt.execute("DELETE FROM proiezione");
            stmt.execute("DELETE FROM slot");
            stmt.execute("DELETE FROM sala");
            stmt.execute("DELETE FROM film");
            stmt.execute("DELETE FROM utente");
            stmt.execute("DELETE FROM sede");
            stmt.execute("SET REFERENTIAL_INTEGRITY TRUE");

            stmt.execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'CineNow Napoli', 'Via Roma', 'Napoli', '80100');");
            stmt.execute("INSERT INTO film (id, titolo, durata, genere, classificazione, descrizione, is_proiettato) " +
                    "VALUES (1, 'Film Test', 120, 'Azione', 'PG-13', 'Descrizione di test', TRUE);");
            stmt.execute("INSERT INTO sala (id, numero, capienza, id_sede) VALUES (1, 1, 100, 1);");
            stmt.execute("INSERT INTO slot (id, ora_inizio) VALUES (1, '18:00:00');");
            stmt.execute("INSERT INTO slot (id, ora_inizio) VALUES (2, '18:30:00');");
            stmt.execute("INSERT INTO slot (id, ora_inizio) VALUES (3, '19:00:00');");
            stmt.execute("INSERT INTO slot (id, ora_inizio) VALUES (4, '19:30:00');");
        } catch (Exception e) {
            throw new RuntimeException("Errore nel reset/seed del database di test", e);
        }
    }

    @BeforeEach
    void setUp() {
        cleanAndSeed();
        slotService = new SlotService();
    }

    @Test
    void testFilmNonEsistente() {
        int filmId = 999;
        int salaId = 1;
        LocalDate d = LocalDate.now().plusDays(1);

        RuntimeException ex = assertThrows(RuntimeException.class,
                () -> slotService.slotDisponibili(filmId, salaId, d, d));
        assertEquals("Film non esistente.", ex.getMessage());
    }

    @Test
    void testSlotDisponibili() throws Exception {
        int filmId = 1, salaId = 1;
        LocalDate d = LocalDate.now().plusDays(1);

        Map<String, Object> result = slotService.slotDisponibili(filmId, salaId, d, d);
        assertNotNull(result);
        assertEquals(120, ((Number) result.get("durataFilm")).intValue());

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> calendar = (List<Map<String, Object>>) result.get("calendar");
        assertEquals(1, calendar.size());

        @SuppressWarnings("unchecked")
        List<Map<String, Object>> slots = (List<Map<String, Object>>) calendar.get(0).get("slots");
        assertEquals(5, slots.size()); // 4 slot inseriti + 1 slot fittizio
        for (Map<String, Object> s : slots) {
            assertFalse(Boolean.TRUE.equals(s.get("occupato")));
        }
    }
}
