package unit.test_gestione_sede;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.dao.ProiezioneDAO;
import it.unisa.application.model.dao.SedeDAO;
import it.unisa.application.model.entity.Film;
import it.unisa.application.model.entity.Proiezione;
import it.unisa.application.model.entity.Sala;
import it.unisa.application.model.entity.Sede;
import it.unisa.application.model.entity.Slot;
import it.unisa.application.sottosistemi.gestione_sede.service.ProgrammazioneSedeService;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;
import unit.test_DAO.DatabaseSetupForTest;

import java.sql.Connection;
import java.sql.Statement;
import java.time.LocalDate;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class ProgrammazioneSedeServiceTest {

    @InjectMocks
    private ProgrammazioneSedeService service;

    @Mock
    private ProiezioneDAO proiezioneDAOMock;

    @Mock
    private SedeDAO sedeDAOMock;

    @BeforeAll
    static void setUpDatabase() {
        DatabaseSetupForTest.configureH2DataSource();
    }

    @BeforeEach
    void setUp() {
        MockitoAnnotations.openMocks(this);
        populateDatabase();
        service = new ProgrammazioneSedeService(proiezioneDAOMock);
    }

    private void populateDatabase() {
        try (Connection connection = DataSourceSingleton.getInstance().getConnection();
             Statement statement = connection.createStatement()) {
            String dataInsertScript = """
                SET REFERENTIAL_INTEGRITY FALSE;
                DELETE FROM prenotazione;
                DELETE FROM proiezione;
                DELETE FROM slot;
                DELETE FROM sala;
                DELETE FROM film;
                DELETE FROM sede;
                DELETE FROM utente;
                DELETE FROM cliente;
                SET REFERENTIAL_INTEGRITY TRUE;

                INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Movieplex', 'Via Roma', 'Napoli', '80100');
                INSERT INTO sala (id, id_sede, numero, capienza) VALUES (1, 1, 1, 100);
                INSERT INTO film (id, titolo, genere, classificazione, durata, descrizione, is_proiettato)
                VALUES (1, 'Avatar', 'Sci-fi', 'T', 180, 'Film di fantascienza', TRUE),
                       (2, 'Inception', 'Thriller', 'T', 148, 'Film sui sogni', TRUE);
                INSERT INTO slot (id, ora_inizio) VALUES (1, '15:00:00'), (2, '18:00:00');
                INSERT INTO proiezione (id, data, id_film, id_sala, id_orario)
                VALUES (1, '2025-01-10', 1, 1, 1),
                       (2, '2025-01-11', 2, 1, 2);
            """;
            statement.execute(dataInsertScript);
            System.out.println("Database popolato con i dati iniziali.");
        } catch (Exception e) {
            throw new RuntimeException("Errore durante il popolamento del database di test", e);
        }
    }

    @Test
    void testGetProgrammazione() {
        int sedeId = 1;
        LocalDate today = LocalDate.now();
        List<Proiezione> proiezioniMock = Arrays.asList(
                new Proiezione(1, new Sala(1), new Film(1, "Avatar", "Sci-fi", "T", 180, null, "Film di fantascienza", true), today.plusDays(1), null, new Slot(1)),
                new Proiezione(2, new Sala(1), new Film(2, "Inception", "Thriller", "T", 148, null, "Film sui sogni", true), today.plusDays(2), null, new Slot(2))
        );
        when(proiezioneDAOMock.retrieveAllBySede(sedeId)).thenReturn(proiezioniMock);
        List<Proiezione> programmazione = service.getProgrammazione(sedeId);
        assertNotNull(programmazione, "La programmazione non dovrebbe essere null.");
        assertEquals(2, programmazione.size(), "La programmazione dovrebbe contenere 2 proiezioni.");
        assertTrue(programmazione.stream().anyMatch(p -> p.getFilmProiezione().getTitolo().equals("Avatar")),
                "La programmazione dovrebbe includere 'Avatar'.");
        System.out.println("Proiezioni trovate: " + programmazione);
    }

    @Test
    void testGetProiezioniFilm() {
        int filmId = 1;
        int sedeId = 1;
        LocalDate today = LocalDate.now();
        List<Proiezione> proiezioniMock = Collections.singletonList(
                new Proiezione(1, new Sala(1), new Film(filmId, "Avatar", "Sci-fi", "T", 180, null, "Film di fantascienza", true), today.plusDays(1), null, new Slot(1))
        );
        when(proiezioneDAOMock.retrieveByFilm(any(Film.class), any(Sede.class))).thenReturn(proiezioniMock);
        List<Proiezione> proiezioniFilm = service.getProiezioniFilm(filmId, sedeId);
        assertNotNull(proiezioniFilm, "Le proiezioni non dovrebbero essere null.");
        assertEquals(1, proiezioniFilm.size(), "Dovrebbe esserci una sola proiezione per il film.");
        assertEquals("Avatar", proiezioniFilm.get(0).getFilmProiezione().getTitolo(),
                "Il titolo del film dovrebbe essere 'Avatar'.");
        System.out.println("Proiezioni trovate: " + proiezioniFilm);
    }

    @Test
    void testGetCatalogoSede() {
        Sede sede = new Sede(1, "Cinema Centrale", "Via Roma");
        List<Film> catalogoMock = Arrays.asList(
                new Film(1, "Avatar", "Sci-fi", "T", 180, null, "Film di fantascienza", true),
                new Film(2, "Inception", "Thriller", "T", 148, null, "Film sui sogni", true)
        );
        try {
            when(sedeDAOMock.retrieveFilm(sede.getId())).thenReturn(catalogoMock);
        } catch (Exception e) {
            fail("Errore durante la configurazione del mock.");
        }
        List<Film> catalogo = service.getCatalogoSede(sede);
        assertNotNull(catalogo, "Il catalogo non dovrebbe essere null.");
        assertEquals(2, catalogo.size(), "Il catalogo dovrebbe contenere 2 film.");
        assertTrue(catalogo.stream().anyMatch(f -> f.getTitolo().equals("Avatar")),
                "Il catalogo dovrebbe includere 'Avatar'.");
        assertTrue(catalogo.stream().anyMatch(f -> f.getTitolo().equals("Inception")),
                "Il catalogo dovrebbe includere 'Inception'.");
        System.out.println("Film trovati nel catalogo: " + catalogo);
    }
}
